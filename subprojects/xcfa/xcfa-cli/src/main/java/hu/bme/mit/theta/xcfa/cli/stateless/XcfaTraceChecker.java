package hu.bme.mit.theta.xcfa.cli.stateless;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceFwBinItpChecker;
import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.refinement.ItpRefutation;
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
		List<XcfaDeclarativeState<?>> sbeStates = new ArrayList<>();
		List<XcfaDeclarativeAction> sbeActions = new ArrayList<>();

		sbeStates.add(trace.getState(0));
		for (int i = 0; i < trace.getActions().size(); ++i) {
			final XcfaEdge edge = XcfaEdge.of(trace.getAction(i).getSource(), trace.getAction(i).getTarget(), trace.getAction(i).getLabels());
			sbeActions.add(XcfaDeclarativeAction.create(edge));
			sbeStates.add(trace.getState(i+1));
		}
		Trace<XcfaDeclarativeState<?>, XcfaDeclarativeAction> sbeTrace = Trace.of(sbeStates, sbeActions);
		final ExprTraceChecker<ItpRefutation> checker = ExprTraceFwBinItpChecker.create(BoolExprs.True(),
				BoolExprs.True(), solverFactory.createItpSolver());
		final ExprTraceStatus<ItpRefutation> status = checker.check(sbeTrace);
		if(status.isInfeasible()) {
			return false;
		} else {
			return true;
		}
	}

}
