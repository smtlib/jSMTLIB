package org.smtlib;


public class JUnitListener implements Log.IListener {
	
	IResponse msg;
	
	@Override
	public void logError(IResponse.IError msg) {
		this.msg = msg;
	}

	@Override
	public void logOut(String msg) {
	}

	@Override
	public void logOut(IResponse result) {
	}

	@Override
	public void logError(String msg) {
	}

	@Override
	public void logDiag(String msg) {
	}

	@Override
	public void indent(String msg) {
	}
}