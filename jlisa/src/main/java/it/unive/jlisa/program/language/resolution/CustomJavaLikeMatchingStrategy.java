package it.unive.jlisa.program.language.resolution;

import it.unive.jlisa.program.type.JavaClassType;
import it.unive.jlisa.program.cfg.JavaParameter;
import it.unive.jlisa.program.type.JavaArrayType;
import it.unive.lisa.program.cfg.Parameter;
import it.unive.lisa.program.cfg.statement.Expression;
import it.unive.lisa.program.cfg.statement.call.Call;
import it.unive.lisa.program.cfg.statement.call.Call.CallType;
import it.unive.lisa.program.language.resolution.ParameterMatchingStrategy;
import it.unive.lisa.type.Type;
import it.unive.jlisa.program.type.JavaReferenceType;
import it.unive.lisa.type.Untyped;
import java.util.Set;

/**
 * A custom java strategy for handle unknown types in static type. If the static
 * type is untyped, we will fallback to the runtime type.
 */
public class CustomJavaLikeMatchingStrategy
	implements ParameterMatchingStrategy {

	/**
	 * The singleton instance of this class.
	 */
	public static final CustomJavaLikeMatchingStrategy INSTANCE = new CustomJavaLikeMatchingStrategy();

	private CustomJavaLikeMatchingStrategy() {
	}

	@Override
	public final boolean matches(
			Call call,
			Parameter[] formals,
			Expression[] actuals,
			Set<Type>[] types) {

		if (formals.length > 0) {
			JavaParameter last_parameter = (JavaParameter) formals[formals.length - 1];

			// if last parameter is varargs then the number of actual
			// arguments shall be >= formals.length - 1
			if (last_parameter.getIsVarargs() && actuals.length < formals.length - 1) {
				return false;
			}

			if (!last_parameter.getIsVarargs() && formals.length != actuals.length)
				return false;
		}

		// for (int i = 0; i < formals.length; i++)
		// 	if (!matches(call, i, formals[i], actuals[i], types[i]))
		// 		return false;

		int n = Math.max(actuals.length, formals.length);
		for (int i = 0; i < n; i++) {
			int againstFormal = Math.min(i, formals.length - 1);
			if (i < actuals.length) {
				if (!matches(call, i, formals[againstFormal], actuals[i], types[i]))
					return false;
			}
		}

		return true;
	}

	public boolean matches(
			Call call,
			int pos,
			Parameter formal,
			Expression actual,
			Set<Type> types) {
		if (call.getCallType() == CallType.INSTANCE && pos == 0)
			return matchReceiver(call, pos, formal, actual, types);
		return matchArgument(call, pos, formal, actual, types);
	}

	private boolean matchReceiver(
			Call call,
			int pos,
			Parameter formal,
			Expression actual,
			Set<Type> types) {
		return types.stream().anyMatch(rt -> rt.canBeAssignedTo(formal.getStaticType()));
	}

	private boolean matchArgument(
			Call call,
			int pos,
			Parameter formal,
			Expression actual,
			Set<Type> types) {
		if (!actual.getStaticType().equals(Untyped.INSTANCE)
				&& actual.getStaticType().canBeAssignedTo(formal.getStaticType()))
			return true;

		assert(formal instanceof JavaParameter);
		JavaParameter parameter = (JavaParameter) formal;
		if (parameter.getIsVarargs()) {
			// TODO: convert formal to base only if the actual is not directly an array. Also in that case, type conversions are not applicable
			assert(parameter.getStaticType() instanceof JavaReferenceType);
			JavaArrayType arrType = (JavaArrayType) ((JavaReferenceType) parameter.getStaticType()).getInnerType();
			Type base = arrType.getBaseType();
			return base.equals(actual.getStaticType());
		}

		for (Type rType : types)
			if (rType.canBeAssignedTo(formal.getStaticType()))
				// equal or widening
				return true;
			else if (JavaClassType.isWrapperOf(formal.getStaticType(), rType))
				// boxing
				return true;
			else if (JavaClassType.isWrapperOf(rType, formal.getStaticType()))
				// unboxing
				return true;
		// TODO the next case should be allowed only when we handle it in the
		// assigning strategy and in the call graph's parameter distance
		// Type unwrapped;
		// else if ((unwrapped = JavaClassType.getUnwrappedType(rType)) != null)
		// unboxing + widening
		// if (unwrapped.canBeAssignedTo(formal.getStaticType()))
		// return true;

		return false;
	}

}
