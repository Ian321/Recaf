package software.coley.recaf.services.phantom.analysis;

import jakarta.annotation.Nonnull;
import jakarta.annotation.Nullable;
import org.objectweb.asm.AnnotationVisitor;
import org.objectweb.asm.ClassWriter;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Type;
import software.coley.recaf.info.ClassInfo;
import software.coley.recaf.info.member.MethodMember;
import software.coley.recaf.services.phantom.PhantomGenerated;
import software.coley.recaf.services.phantom.model.PhantomClassConstraint;
import software.coley.recaf.services.phantom.model.PhantomFieldRequirement;
import software.coley.recaf.services.phantom.model.PhantomInnerRequirement;
import software.coley.recaf.services.phantom.model.PhantomMethodRequirement;
import software.coley.recaf.util.JavaVersion;
import software.coley.recaf.util.Types;

import java.util.Map;

import static org.objectweb.asm.Opcodes.*;

/**
 * Emitter for resolved phantom classes.
 *
 * @author Matt Coley
 */
public class PhantomClassWriter {
	private static final String GENERATED_MARKER_DESC = Type.getDescriptor(PhantomGenerated.class);
	private static final String RETENTION_DESC = "Ljava/lang/annotation/Retention;";
	private static final String RETENTION_POLICY_DESC = "Ljava/lang/annotation/RetentionPolicy;";

	private PhantomClassWriter() {}

	/**
	 * @param constraint
	 * 		Resolved class constraint.
	 * @param constraints
	 * 		All resolved constraints, used for nested-class metadata.
	 * @param targetVersion
	 * 		Java language version that will consume the generated class.
	 * @param lookup
	 * 		Known type lookup used to select an accessible superclass constructor.
	 *
	 * @return Generated class bytes.
	 */
	@Nonnull
	public static byte[] write(@Nonnull PhantomClassConstraint constraint,
	                           @Nonnull Map<String, PhantomClassConstraint> constraints,
	                           int targetVersion,
	                           @Nullable ClassLookup lookup) {
		boolean isAnnotation = constraint.isAnnotation();
		boolean isInterface = constraint.isInterface();
		int access = ACC_PUBLIC;
		if (isInterface)
			access |= ACC_INTERFACE | ACC_ABSTRACT;
		if (isAnnotation)
			access |= ACC_ANNOTATION;
		if (constraint.isEnum())
			access |= ACC_ENUM | ACC_FINAL;

		int version = JavaVersion.adaptFromLanguageVersion(targetVersion);
		ClassWriter writer = new ClassWriter(0);
		String[] interfaces = constraint.getResolvedInterfaces().isEmpty() ?
				null : constraint.getResolvedInterfaces().toArray(String[]::new);
		writer.visit(version, access, constraint.getName(), genericClassSignature(constraint), constraint.getResolvedSuperName(), interfaces);

		// Mark generated phantoms so other tooling can recognize synthetic placeholders.
		writer.visitAnnotation(GENERATED_MARKER_DESC, true).visitEnd();

		// Synthetic annotation phantoms need a retention policy to compile source usage correctly.
		if (isAnnotation) {
			AnnotationVisitor retention = writer.visitAnnotation(RETENTION_DESC, true);
			retention.visitEnum("value", RETENTION_POLICY_DESC,
					constraint.hasRuntimeVisibleAnnotationEvidence() ? "RUNTIME" : "CLASS");
			retention.visitEnd();
		}

		if (constraint.getOuterName() != null) {
			writer.visitInnerClass(constraint.getName(), constraint.getOuterName(), constraint.getInnerSimpleName(),
					innerClassAccess(constraint, constraint.getInnerClassAccess()));
		}
		for (PhantomInnerRequirement inner : constraint.getDeclaredInners()) {
			writer.visitInnerClass(inner.innerName(), constraint.getName(), inner.innerSimpleName(),
					innerClassAccess(constraints.get(inner.innerName()), constraint.getDeclaredInnerAccess(inner.innerName())));
		}

		if (constraint.isEnum()) {
			String enumDescriptor = 'L' + constraint.getName() + ';';
			for (String enumConstant : constraint.getEnumConstants())
				writer.visitField(ACC_PUBLIC | ACC_STATIC | ACC_FINAL | ACC_ENUM,
						enumConstant, enumDescriptor, null, null).visitEnd();
		}

		for (PhantomFieldRequirement field : constraint.getFieldRequirements()) {
			int fieldAccess = ACC_PUBLIC;
			if (isInterface || field.isStatic())
				fieldAccess |= ACC_STATIC;
			if (isInterface)
				fieldAccess |= ACC_FINAL;
			writer.visitField(fieldAccess, field.getName(), field.getDescriptor(), null, null).visitEnd();
		}

		if (!isInterface) {
			if (constraint.isEnum()) {
				writeEnumConstructor(writer, constraint.getResolvedSuperName());
			} else {
				String superConstructorDescriptor = superConstructorDescriptor(constraint.getResolvedSuperName(), constraints, lookup);
				writeConstructor(writer, constraint.getResolvedSuperName(), "()V", superConstructorDescriptor);
			}
			for (PhantomMethodRequirement method : constraint.getMethodRequirements()) {
				if (method.isConstructor() && !"()V".equals(method.getDescriptor()))
					writeConstructor(writer, constraint.getResolvedSuperName(), method.getDescriptor(),
							superConstructorDescriptor(constraint.getResolvedSuperName(), constraints, lookup));
			}
		}

		for (PhantomMethodRequirement method : constraint.getMethodRequirements()) {
			if (method.isConstructor())
				continue;
			writeMethod(writer, method, isInterface);
		}

		writer.visitEnd();
		return writer.toByteArray();
	}

	@Nullable
	private static String genericClassSignature(@Nonnull PhantomClassConstraint constraint) {
		int count = constraint.getGenericParameterCount();
		if (count == 0)
			return null;
		StringBuilder signature = new StringBuilder("<");
		for (int i = 0; i < count; i++)
			signature.append('T').append(i).append(":Ljava/lang/Object;");
		signature.append('>').append('L').append(constraint.getResolvedSuperName()).append(';');
		for (String interfaceName : constraint.getResolvedInterfaces())
			signature.append('L').append(interfaceName).append(';');
		return signature.toString();
	}

	private static int innerClassAccess(@Nullable PhantomClassConstraint constraint, int metadataAccess) {
		int access = metadataAccess & (ACC_PUBLIC | ACC_PRIVATE | ACC_PROTECTED | ACC_STATIC | ACC_FINAL | ACC_ABSTRACT | ACC_INTERFACE | ACC_ANNOTATION | ACC_ENUM);
		if (access == 0)
			access = ACC_PUBLIC | ACC_STATIC;
		if (constraint == null)
			return access;
		if (constraint.isInterface())
			access |= ACC_INTERFACE | ACC_ABSTRACT;
		if (constraint.isAnnotation())
			access |= ACC_ANNOTATION;
		if (constraint.isEnum())
			access |= ACC_ENUM | ACC_FINAL;
		return access;
	}

	private static void writeConstructor(@Nonnull ClassWriter writer, @Nonnull String superName,
	                                     @Nonnull String descriptor, @Nonnull String superDescriptor) {
		MethodVisitor visitor = writer.visitMethod(ACC_PUBLIC, "<init>", descriptor, null, null);
		visitor.visitCode();
		visitor.visitVarInsn(ALOAD, 0);
		int stackSize = 1;
		for (Type argumentType : Type.getArgumentTypes(superDescriptor)) {
			pushDefaultValue(visitor, argumentType);
			stackSize += argumentType.getSize();
		}
		visitor.visitMethodInsn(INVOKESPECIAL, superName, "<init>", superDescriptor, false);
		visitor.visitInsn(RETURN);
		visitor.visitMaxs(stackSize, localSize(descriptor, false));
		visitor.visitEnd();
	}

	private static void writeEnumConstructor(@Nonnull ClassWriter writer, @Nonnull String superName) {
		MethodVisitor visitor = writer.visitMethod(ACC_PRIVATE, "<init>", "(Ljava/lang/String;I)V", null, null);
		visitor.visitCode();
		visitor.visitVarInsn(ALOAD, 0);
		visitor.visitVarInsn(ALOAD, 1); // name
		visitor.visitVarInsn(ILOAD, 2); // ordinal
		visitor.visitMethodInsn(INVOKESPECIAL, superName, "<init>", "(Ljava/lang/String;I)V", false);
		visitor.visitInsn(RETURN);
		visitor.visitMaxs(3, 3);
		visitor.visitEnd();
	}

	@Nonnull
	private static String superConstructorDescriptor(@Nonnull String superName,
	                                                 @Nonnull Map<String, PhantomClassConstraint> constraints,
	                                                 @Nullable ClassLookup lookup) {
		// Generated phantom parents always have a public no-argument constructor available.
		PhantomClassConstraint phantomSuper = constraints.get(superName);
		if (phantomSuper != null)
			return "()V";

		// If the super class is known, then we can try to find an accessible constructor to call.
		if (lookup != null) {
			ClassInfo knownSuper = lookup.getKnownClassInfo(superName);
			if (knownSuper != null) {
				MethodMember noArg = knownSuper.getDeclaredMethod("<init>", "()V");
				if (isAccessible(noArg))
					return "()V";
				for (MethodMember method : knownSuper.getMethods())
					if ("<init>".equals(method.getName()) && isAccessible(method))
						return method.getDescriptor();
			}
		}

		// If there isn't a known super class, or if the known super class has no accessible constructors,
		// then we have to fall back to a no-argument constructor.
		return "()V";
	}

	private static boolean isAccessible(@Nullable MethodMember method) {
		return method != null && (method.hasPublicModifier() || method.hasProtectedModifier());
	}

	private static void pushDefaultValue(@Nonnull MethodVisitor visitor, @Nonnull Type type) {
		switch (type.getSort()) {
			case Type.LONG -> visitor.visitInsn(LCONST_0);
			case Type.FLOAT -> visitor.visitInsn(FCONST_0);
			case Type.DOUBLE -> visitor.visitInsn(DCONST_0);
			case Type.OBJECT, Type.ARRAY -> visitor.visitInsn(ACONST_NULL);
			default -> visitor.visitInsn(ICONST_0);
		}
	}

	private static void writeMethod(@Nonnull ClassWriter writer,
	                                @Nonnull PhantomMethodRequirement method,
	                                boolean ownerIsInterface) {
		boolean isAbstract = ownerIsInterface && !method.isStatic();
		int access = ACC_PUBLIC;
		if (method.isStatic())
			access |= ACC_STATIC;
		if (isAbstract)
			access |= ACC_ABSTRACT;

		MethodVisitor visitor = writer.visitMethod(access, method.getName(), method.getDescriptor(), null, null);
		if (isAbstract) {
			visitor.visitEnd();
			return;
		}

		// Stub out the method body based on the return type.
		visitor.visitCode();
		Type returnType = Type.getReturnType(method.getDescriptor());
		switch (returnType.getSort()) {
			case Type.VOID -> {
				visitor.visitInsn(RETURN);
				visitor.visitMaxs(0, localSize(method.getDescriptor(), method.isStatic()));
			}
			case Type.BOOLEAN, Type.BYTE, Type.CHAR, Type.SHORT, Type.INT -> {
				visitor.visitInsn(ICONST_0);
				visitor.visitInsn(IRETURN);
				visitor.visitMaxs(1, localSize(method.getDescriptor(), method.isStatic()));
			}
			case Type.LONG -> {
				visitor.visitInsn(LCONST_0);
				visitor.visitInsn(LRETURN);
				visitor.visitMaxs(2, localSize(method.getDescriptor(), method.isStatic()));
			}
			case Type.FLOAT -> {
				visitor.visitInsn(FCONST_0);
				visitor.visitInsn(FRETURN);
				visitor.visitMaxs(1, localSize(method.getDescriptor(), method.isStatic()));
			}
			case Type.DOUBLE -> {
				visitor.visitInsn(DCONST_0);
				visitor.visitInsn(DRETURN);
				visitor.visitMaxs(2, localSize(method.getDescriptor(), method.isStatic()));
			}
			default -> {
				visitor.visitInsn(ACONST_NULL);
				visitor.visitInsn(ARETURN);
				visitor.visitMaxs(1, localSize(method.getDescriptor(), method.isStatic()));
			}
		}
		visitor.visitEnd();
	}

	private static int localSize(@Nonnull String descriptor, boolean isStatic) {
		return (isStatic ? 0 : 1) + Types.countParameterSlots(Type.getMethodType(descriptor));
	}
}
