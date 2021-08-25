package hu.bme.mit.theta.frontend.transformation.grammar.expression;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.UnaryExpr;

public class Reference<R extends Type, T extends Type> extends UnaryExpr<T, R> {
	private static final int HASH_SEED = 6987;
	private static final String label = "&";
	private static int COUNTER = 0;
	private final int id;
	private final R ptrType;

	private Reference(Expr<T> op, R ptrType, int id) {
		super(op);
		this. ptrType = ptrType;
		this.id = id;
	}

	public static <R extends Type, T extends Type> Reference<R, T> of(Expr<T> op, R ptrType) {
		return new Reference<>(op, ptrType, COUNTER++);
	}

	public static <R extends Type, T extends Type> Reference<R, T> of(Expr<T> op, R ptrType, int id) {
		return new Reference<>(op, ptrType, id);
	}

	@Override
	public R getType() {
		return ptrType;
	}

	@Override
	public LitExpr<R> eval(Valuation val) {
		throw new IllegalStateException("Reference/Dereference expressions are not meant to be evaluated!");
	}

	@Override
	public UnaryExpr<T, R> with(Expr<T> op) {
		return of(op, ptrType, id);
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	public String getOperatorLabel() {
		return label;
	}

	public int getId() {
		return id;
	}
}