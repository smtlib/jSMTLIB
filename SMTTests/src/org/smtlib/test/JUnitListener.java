package org.smtlib.test;

import java.util.LinkedList;
import java.util.List;

import org.smtlib.IResponse;
import org.smtlib.Log;


/** A {@link Log.IListener} used by the parsing/type-checking test base classes
 *  (e.g. {@link LogicsBase}, {@link TypeCheckRoot}, {@link ParseCommand},
 *  {@link ParseExpressions}, {@link ParseExpressionErrors}, {@link RoundTripTest},
 *  {@link LogicTests}) to capture errors reported through {@code smtConfig.log} rather than
 *  printing them.
 *
 *  Parsing and type-checking errors are often reported as a side effect, via
 *  {@code log.logError(...)}, rather than solely through the return value of the call under
 *  test -- so a test cannot always tell whether an error was reported just by inspecting what
 *  the API returned. Each of the classes above installs a JUnitListener in its {@code @Before}
 *  setup (usually after {@code log.clearListeners()}, to remove the default listener that
 *  would otherwise print errors to the console during the test run) and then, after invoking
 *  the code under test, asserts against {@link #msgs} to check which errors, if any, were
 *  logged. All other Log.IListener callbacks are no-ops, so only IError messages are captured;
 *  everything else is silently dropped instead of cluttering test output. */
public class JUnitListener implements Log.IListener {
	
	List<IResponse> msgs = new LinkedList<IResponse>();
	
	@Override
	public void logError(IResponse.IError msg) {
		this.msgs.add(msg);
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