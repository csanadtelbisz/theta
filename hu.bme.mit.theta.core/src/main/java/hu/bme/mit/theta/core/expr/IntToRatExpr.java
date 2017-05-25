package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class IntToRatExpr extends UnaryExpr<IntType, RatType> {
	private static final int HASH_SEED = 1627;
	private static final String OPERATOR_LABEL = "ToRat";

	IntToRatExpr(final Expr<? extends IntType> op) {
		super(op);
	}

	@Override
	public RatType getType() {
		return Types.Rat();
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public IntToRatExpr withOp(final Expr<? extends IntType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return Exprs.ToRat(op);
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}