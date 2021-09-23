package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public final class FpIsNanExpr extends UnaryExpr<FpType, BoolType> {

	private static final int HASH_SEED = 1786;
	private static final String OPERATOR_LABEL = "isnan";

	private FpIsNanExpr(final Expr<FpType> op) {
		super(op);
		checkAllTypesEqual(op);
	}

	public static FpIsNanExpr of(final Expr<FpType> op) {
		return new FpIsNanExpr(op);
	}

	public static FpIsNanExpr create(final Expr<?> op) {
		final Expr<FpType> newOp = castFp(op);
		return FpIsNanExpr.of(newOp);
	}

	@Override
	public UnaryExpr with(Expr op) {
		if (op == getOp()) {
			return this;
		} else {
			return FpIsNanExpr.of(op);
		}
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Valuation val) {
		final FpLitExpr opVal = (FpLitExpr) getOp().eval(val);

		return Bool(opVal.isNaN());
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FpIsNanExpr) {
			final FpIsNanExpr that = (FpIsNanExpr) obj;
			return this.getOp().equals(that.getOp());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}
}
 
