package hu.bme.mit.theta.xcfa.cli.stateless;

public enum ErrorCode {
	FRONTEND_FAIL(-80, "Verification ERROR: Frontend (parsing) failed"),
	PORTFOLIO_TIMEOUT(-43, "Verification TIMEOUT: Portfolio timed out"),
	CANNOT_CREATE_CFA(-50, "Verification ERROR: Cannot transform XCFA into CFA"),
	STUCK(-30, "Verification ERROR: Configuration failed (stuck)");

	public final int code;
	public final String msg;

	private ErrorCode(int code, String msg) {
		this.code = code;
		this.msg = msg;
	}
}
