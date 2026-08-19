package it.unive.jlisa.program.java.constructs.classmetatype;

import it.unive.jlisa.program.type.*;
import it.unive.lisa.analysis.AbstractDomain;
import it.unive.lisa.analysis.AbstractLattice;
import it.unive.jlisa.program.cfg.statement.literal.IntLiteral;
import it.unive.lisa.analysis.Analysis;
import it.unive.lisa.analysis.AnalysisState;
import it.unive.jlisa.program.cfg.expression.JavaNewArray;
import it.unive.lisa.lattices.ExpressionSet;
import it.unive.lisa.lattices.Satisfiability;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.StatementStore;
import it.unive.lisa.interprocedural.InterproceduralAnalysis;
import it.unive.lisa.program.cfg.CFG;
import it.unive.lisa.program.cfg.CodeLocation;
import it.unive.lisa.program.cfg.statement.Expression;
import it.unive.lisa.program.cfg.statement.PluggableStatement;
import it.unive.lisa.program.cfg.statement.Statement;
import it.unive.lisa.symbolic.SymbolicExpression;
import it.unive.lisa.symbolic.heap.AccessChild;
import it.unive.lisa.symbolic.heap.HeapDereference;
import it.unive.lisa.symbolic.heap.HeapReference;
import it.unive.lisa.symbolic.value.GlobalVariable;
import it.unive.jlisa.program.SyntheticCodeLocationManager;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLt;
import it.unive.lisa.type.Type;
import it.unive.lisa.type.Untyped;

public class ClassGetMethods extends it.unive.lisa.program.cfg.statement.UnaryExpression implements PluggableStatement {

	private SyntheticCodeLocationManager synGen;

	protected Statement originating;

	public ClassGetMethods(
			CFG cfg,
			CodeLocation location,
			Expression expr) {
		super(cfg, location, "getMethods", JavaClassType.getClassMetaType(), expr);
		synGen = new SyntheticCodeLocationManager("copy-methods-" + this.getLocation().toString());
	}

	public static ClassGetMethods build(
			CFG cfg,
			CodeLocation location,
			Expression... params) {
		return new ClassGetMethods(cfg, location, params[0]);
	}

	@Override
	public void setOriginatingStatement(
			Statement st) {
		originating = st;
	}

	@Override
	public <A extends AbstractLattice<A>, D extends AbstractDomain<A>> AnalysisState<A> fwdUnarySemantics(
			InterproceduralAnalysis<A, D> interprocedural,
			AnalysisState<A> state,
			SymbolicExpression expr,
			StatementStore<A> expressions)
			throws SemanticException {

		Analysis<A, D> analysis = interprocedural.getAnalysis();
		CodeLocation location = getLocation();

		Type classMetaType = JavaClassType.getClassMetaType();
		JavaReferenceType refMethodArrType = JavaArrayType.METHOD_ARRAY;
		JavaReferenceType refMethodType = new JavaReferenceType(JavaClassType.getMethodType());

		GlobalVariable var = new GlobalVariable(Untyped.INSTANCE, "declaredMethods", location);
		GlobalVariable lengthVar = new GlobalVariable(Untyped.INSTANCE, "length", location);

		// access source arr length
		HeapDereference derefExpr = new HeapDereference(classMetaType, expr, location);
		AccessChild accessExpr = new AccessChild(refMethodArrType, derefExpr, var, location);
		HeapDereference derefSourceArr = new HeapDereference(refMethodArrType.getInnerType(), accessExpr, location);
		AccessChild accessSourceLen = new AccessChild(JavaIntType.INSTANCE, derefSourceArr, lengthVar, location);

		// alloc new array
		IntLiteral zero = new IntLiteral(getCFG(), location, 0);
		Constant c = new Constant(JavaIntType.INSTANCE, 0, location);
		JavaNewArray newArr = new JavaNewArray(getCFG(), location, zero, refMethodArrType);

		AnalysisState<A> methodsAllocated = newArr.fwdUnarySemantics(interprocedural, state, c, expressions);

		AnalysisState<A> tmp = methodsAllocated;

		int methodCount = 0;
		boolean outOfBoundsMethodArr = false;

		while (outOfBoundsMethodArr == false) {

			Constant idx = new Constant(JavaIntType.INSTANCE, methodCount, location);

			it.unive.lisa.symbolic.value.BinaryExpression withinBounds = new it.unive.lisa.symbolic.value.BinaryExpression(
					JavaBooleanType.INSTANCE,
					idx, accessSourceLen, ComparisonLt.INSTANCE, location);

			Satisfiability sat = analysis.satisfies(state, withinBounds, this);
			if (sat != Satisfiability.SATISFIED) {
				outOfBoundsMethodArr = true;
				break;
			}

			AccessChild accessSourceCell = new AccessChild(refMethodType, derefSourceArr, idx, location);

			for (SymbolicExpression allocated : methodsAllocated.getExecutionExpressions()) {
				HeapDereference derefArr = new HeapDereference(refMethodArrType.getInnerType(), allocated, location);
				AccessChild accessDestCell = new AccessChild(refMethodType, derefArr, idx, location);

				ClassCopyMethod copyMethod = new ClassCopyMethod(getCFG(), synGen.nextLocation(), this);
				tmp = copyMethod.copyAndStore(interprocedural, tmp, accessSourceCell, accessDestCell, expressions);
			}

			++methodCount;
		}

		c = new Constant(JavaIntType.INSTANCE, methodCount, location);
		for (SymbolicExpression allocated : methodsAllocated.getExecutionExpressions()) {
			HeapDereference derefArr = new HeapDereference(refMethodArrType.getInnerType(), allocated, location);
			AccessChild accessDestLen = new AccessChild(JavaIntType.INSTANCE, derefArr, lengthVar, location);
			tmp = analysis.assign(tmp, accessDestLen, c, this);
		}

		ExpressionSet exprs = methodsAllocated.getExecutionExpressions();
		AnalysisState<A> res = tmp;
		for (SymbolicExpression e : exprs) {
			res = res.lub(analysis.smallStepSemantics(res, e, this));
		}
		return res;
	}

	@Override
	protected int compareSameClassAndParams(
			Statement o) {
		return 0;
	}

}
