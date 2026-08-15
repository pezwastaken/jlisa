package it.unive.jlisa.program.cfg.expression;

import it.unive.lisa.analysis.AbstractDomain;
import it.unive.lisa.analysis.AbstractLattice;
import it.unive.lisa.analysis.AnalysisState;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.StatementStore;
import it.unive.lisa.interprocedural.InterproceduralAnalysis;
import it.unive.lisa.program.cfg.CFG;
import it.unive.lisa.program.cfg.CodeLocation;
import it.unive.lisa.program.cfg.statement.Expression;
import it.unive.lisa.program.cfg.statement.Statement;
import it.unive.lisa.symbolic.SymbolicExpression;

import it.unive.lisa.program.cfg.statement.comparison.NotEqual;
import it.unive.lisa.program.cfg.statement.logic.Not;

public class JavaComparisonNotEqual extends NotEqual {

	/**
	 * Builds the equality test.
	 * 
	 * @param cfg      the {@link CFG} where this operation lies
	 * @param location the location where this literal is defined
	 * @param left     the left-hand side of this operation
	 * @param right    the right-hand side of this operation
	 */
	public JavaComparisonNotEqual(
			CFG cfg,
			CodeLocation location,
			Expression left,
			Expression right) {
		super(cfg, location, left, right);
	}

	@Override
	protected int compareSameClassAndParams(
			Statement o) {
		return 0; // no extra fields to compare
	}

	@Override
	public <A extends AbstractLattice<A>, D extends AbstractDomain<A>> AnalysisState<A> fwdBinarySemantics(
			InterproceduralAnalysis<A, D> interprocedural,
			AnalysisState<A> state,
			SymbolicExpression left,
			SymbolicExpression right,
			StatementStore<A> expressions)
			throws SemanticException {

		CodeLocation location = getLocation();

		JavaComparisonEqual eq = new JavaComparisonEqual(getCFG(), location, getLeft(), getRight());
		Not not = new Not(getCFG(), location, eq);
		AnalysisState<A> tmp = not.forwardSemantics(state, interprocedural, expressions);

		return tmp;
	}

}
