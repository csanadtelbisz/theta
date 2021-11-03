package hu.bme.mit.theta.xcfa.cli.stateless;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceNoItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
import hu.bme.mit.theta.analysis.expr.refinement.Refutation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xcfa.analysis.declarative.XcfaDeclarativeAction;
import hu.bme.mit.theta.xcfa.analysis.declarative.XcfaDeclarativeState;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;

import java.util.ArrayList;
import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;

public class XcfaTraceChecker {
	public static boolean isTraceFeasible(
			final Trace<XcfaDeclarativeState<?>, XcfaDeclarativeAction> trace, SolverFactory solverFactory) {
		/*
		final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(BoolExprs.True(),
				BoolExprs.True(), solverFactory.createItpSolver());
		 */
		final ExprTraceChecker<Refutation> checker = ExprTraceNoItpChecker.create(BoolExprs.True(),
				BoolExprs.True(), solverFactory.createSolver());
		final ExprTraceStatus<Refutation> status = checker.check(trace);
		if(status.isInfeasible()) {
			return false;
		} else {
			return true;
		}
	}

}
