package hu.bme.mit.theta.xsts.analysis.autoexpl;

import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.AutoExpl;
import hu.bme.mit.theta.analysis.expr.refinement.autoexpl.NewAtomsAutoExpl;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtAtomCollector;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Set;
import java.util.stream.Collectors;

public class XstsNewAtomsAutoExpl implements XstsAutoExpl{
    @Override
    public AutoExpl create(XSTS xsts) {
        final Set<Expr<BoolType>> atoms = Containers.createSet();
        atoms.addAll(StmtAtomCollector.collectAtoms(xsts.getEnv()));
        atoms.addAll(StmtAtomCollector.collectAtoms(xsts.getInit()));
        atoms.addAll(StmtAtomCollector.collectAtoms(xsts.getTran()));
        atoms.addAll(ExprUtils.getAtoms(xsts.getProp()));
        atoms.addAll(ExprUtils.getAtoms(xsts.getInitFormula()));

        final Set<Expr<BoolType>> canonicalAtoms = atoms.stream()
                .map(ExprUtils::canonize)
                .flatMap(atom -> ExprUtils.getAtoms(atom).stream())
                .collect(Collectors.toSet());
        return new NewAtomsAutoExpl(xsts.getCtrlVars(),canonicalAtoms,0);
    }
}
