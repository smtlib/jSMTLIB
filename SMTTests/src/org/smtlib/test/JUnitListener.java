package org.smtlib.test;

import java.util.LinkedList;
import java.util.List;

import org.smtlib.IResponse;
import org.smtlib.Log;
import org.smtlib.impl.Response;


/** A {@link Log.IListener} used by the parsing/type-checking test base classes
 *  (e.g. {@link LogicsBase}, {@link ParseCommand}, {@link ParseExpressions},
 *  {@link ParseExpressionErrors}, {@link RoundTripTest}, {@link LogicTests}) to capture
 *  errors reported through {@code smtConfig.log} rather than printing them.
 *
 *  Parsing and type-checking errors are often reported as a side effect, via
 *  {@code log.logError(...)}, rather than solely through the return value of the call under
 *  test -- so a test cannot always tell whether an error was reported just by inspecting what
 *  the API returned. Each of the classes above installs a JUnitListener in its {@code @Before}
 *  setup (usually after {@code log.clearListeners()}, to remove the default listener that
 *  would otherwise print errors to the console during the test run) and then, after invoking
 *  the code under test, asserts against {@link #msgs} to check which errors, if any, were
 *  logged.
 *
 *  Both logError overloads are captured into {@link #msgs}: the {@code IResponse.IError} one
 *  directly, and the plain-{@code String} one by wrapping it in a {@link Response.Error} so
 *  callers can treat both uniformly. Earlier the String overload was a no-op, which meant a
 *  real error reported that way was invisible to both the test assertions and the console
 *  (since clearListeners() removes the listener that would otherwise have printed it) -- a
 *  test asserting msgs.isEmpty() could pass even though an error had actually been logged.
 *  logOut/logDiag remain no-ops: those are success-path output and (mostly verbose-gated)
 *  trace messages, not error signal.
 *
 *  The two logError paths arise from different situations and are not quite interchangeable:
 *  - {@code logError(IResponse.IError)} is used once a full response object already exists --
 *    typically {@code responseFactory.error(msg, pos)} constructed with the offending source
 *    position -- and is usually also the value returned to the caller as the command's actual
 *    result (e.g. SMT.java's parse/validation/type-check error handling, Utils.java's
 *    SMTLIBException sites). These almost always carry a non-null {@code pos()}.
 *  - {@code logError(String)} is used for lower-level, defensive diagnostics that have no
 *    convenient source position at hand and are not necessarily the operation's return value
 *    (e.g. Utils.unescape's malformed-string-literal checks, or SMT.java's "Could not find
 *    file" report). Wrapped via {@link Response.Error#Error(String)}, these always have
 *    {@code pos() == null}.
 *
 *  Because both land in the same ordered list, a String-path error logged before an
 *  IError-path one (e.g. a malformed string literal noticed by the lexer while it is still
 *  scanning a token, ahead of the parser-level error the surrounding command eventually
 *  produces) would sit at {@code msgs.get(0)} with a null {@code pos()}. Several consumers --
 *  e.g. {@link ParseExpressionErrors#testExpr} -- call {@code pos().charStart()} on
 *  {@code msgs.get(0)} unconditionally, assuming it is always a positioned IError; that would
 *  NullPointerException. No current test input triggers this ordering, so it is a known,
 *  currently-unaddressed gap rather than an observed failure -- accepted for now because
 *  fixing it properly (either splitting the two paths into separate lists, or having every
 *  such consumer null-check {@code pos()}) requires touching each consumer, not just this
 *  listener; see the class discussion for why the lists were kept merged regardless. */
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
		this.msgs.add(new Response.Error(msg));
	}

	@Override
	public void logDiag(String msg) {
	}

	@Override
	public void indent(String msg) {
	}
}