/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.List;

import org.smtlib.*;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IKeyword;

/** This class is an adapter for Bitwuzla (bit-vectors, floating-point, arrays and
 *  uninterpreted functions -- no arithmetic logics, no datatypes). It is a concrete,
 *  silent inheritor of {@link AbstractSolver} apart from a handful of real, empirically
 *  confirmed (against 0.9.1) protocol gaps:
 *  <p>
 *  1) Bitwuzla has genuinely no {@code get-info}, {@code get-option}, {@code
 *  get-assignment}, or {@code get-proof} support at all -- each is rejected with {@code
 *  [error] <stdin>:L:C: unsupported command '...'} and, critically, that rejection
 *  KILLS the process (see point 2), so these four must be answered entirely client-side
 *  and never forwarded. {@link #get_option} therefore tracks values itself (via the
 *  inherited {@code options} map, falling back to {@code smtConfig.utils.defaults})
 *  rather than relying on AbstractSolver's default of asking the solver.
 *  <p>
 *  2) Unlike cvc5/yices2 (which die only after some errors), Bitwuzla's process exits
 *  immediately after essentially ANY error -- an unsupported command, an unsupported
 *  logic, a sort mismatch in an assertion, etc. -- not just protocol violations. {@link
 *  #selfReportsImmediateExit()} is therefore true, and {@code :error-behavior} is
 *  reported (via the hardcoded {@link #get_info}) as {@code immediate-exit}, which is
 *  simply the truth for this solver, not a workaround.
 *  <p>
 *  3) Bitwuzla's own error text for a genuine semantic error (e.g. {@code [error]
 *  <stdin>:3:14: expected terms of same sort ...}) is not SMT-LIB {@code (error "...")}
 *  syntax -- the leading {@code [} is not valid s-expression syntax at all, and feeding
 *  it to the standard parser doesn't just fail to parse cleanly, it throws a raw {@code
 *  ClassCastException} out of the lexer (a LexError token reaching code that assumes an
 *  IError) instead of the {@code IParser.ParserException} that {@link
 *  AbstractSolver#parseResponse} already knows how to turn into a clean error response.
 *  {@link #parseResponse} widens that catch locally so a non-conforming response
 *  produces an ordinary error IResponse instead of crashing the whole run. */
public class Solver_bitwuzla extends AbstractSolver implements ISolver {

	@Override
	protected boolean selfReportsImmediateExit() { return true; }

	/** The command-line arguments for launching the solver. */
	protected String cmds[];

	/** Creates an instance of the solver */
	public Solver_bitwuzla(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		this.smtConfig = smtConfig;
		List<String> args = new java.util.ArrayList<String>(Arrays.asList(executable,"--lang","smt2"));
		if (smtConfig.seed != 0) {
			args.add("--seed");
			args.add(Integer.toString(smtConfig.seed));
		}
		if (smtConfig.timeout > 0) {
			// --time-limit-per is a per-check-sat timeout in milliseconds (matching
			// smtConfig.timeout's per-query semantics, as opposed to --time-limit,
			// which is a single limit for the whole run).
			args.add("--time-limit-per");
			args.add(Integer.toString((int)Math.ceil(smtConfig.timeout * 1000)));
		}
		cmds = args.toArray(new String[args.size()]);
		// Bitwuzla prints no interactive prompt, so "\n" is the right end marker.
		solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
	}

	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			// Bitwuzla's own :print-success default is false (unlike e.g. cvc5, which
			// has a CLI flag for this) -- without explicitly turning it on at the wire
			// level, ordinary accepted commands (set-logic, declare-const, assert, ...)
			// produce no response at all, and sendAndListen just hangs waiting for one.
			solverProcess.sendAndListen("(set-option :print-success true)\n");
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started " + smtConfig.solvername);
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}

	@Override
	protected IResponse parseResponse(String response) {
		IResponse result;
		try {
			result = super.parseResponse(response);
		} catch (RuntimeException e) {
			return smtConfig.responseFactory.error("Unexpected (non-SMT-LIB) response from bitwuzla: " + response);
		}
		// Parser.parseResponse's fallback for response text that doesn't match any
		// recognized shape (success/sat/error/.../get-info attribute list) just returns
		// whatever the generic sexpr parser produced -- for bitwuzla's non-SMT-LIB
		// "[error] <stdin>:L:C: msg" diagnostic lines, the lexer chokes on the leading
		// '[' and that comes back as a bare lex-error token which satisfies isError()
		// but is NOT actually an IResponse.IError -- callers that safely narrow any
		// isError()==true response to IResponse.IError (e.g. SMT.java's own script
		// loop) get a ClassCastException instead of a clean error message. Catch that
		// shape here and manufacture a real one.
		if (result != null && result.isError() && !(result instanceof IResponse.IError)) {
			return smtConfig.responseFactory.error("Unexpected (non-SMT-LIB) response from bitwuzla: " + response);
		}
		return result;
	}

	@Override
	protected IResponse set_option_impl(IKeyword key, IAttributeValue value) {
		IResponse r = checkPrintSuccess(smtConfig, key, value);
		if (r != null) return r;
		options.put(key.value(), value);
		return sendCommand(smtConfig.commandFactory.set_option(key, value));
	}

	/** Answered entirely client-side (never forwarded -- see class comment point 1):
	 *  from whatever this run has set via {@link #set_option_impl}, falling back to the
	 *  standard SMT-LIB default for any option never set, and "unsupported" for anything
	 *  not a recognized standard option at all (matching what a compliant solver would
	 *  say about an option it doesn't have). */
	@Override
	public IResponse get_option(IKeyword key) {
		if (key.equals(printSuccess)) return smtConfig.nosuccess ? Utils.FALSE : Utils.TRUE;
		String opt = key.value();
		IAttributeValue value = options.get(opt);
		if (value == null) value = smtConfig.utils.defaults.get(opt);
		if (value == null) return smtConfig.responseFactory.unsupported();
		return value;
	}

	/** Answered entirely client-side (never forwarded -- see class comment point 1).
	 *  :version/:authors are fixed to the 0.9.1 build this adapter was written and
	 *  tested against; if jsmtlib.properties is ever pointed at a different Bitwuzla
	 *  build, update these to match. */
	@Override
	public IResponse get_info(IKeyword key) {
		IAttributeValue lit;
		if (Utils.ERROR_BEHAVIOR.equals(key)) {
			lit = smtConfig.exprFactory.symbol(Utils.IMMEDIATE_EXIT);
		} else if (Utils.AUTHORS.equals(key)) {
			lit = smtConfig.exprFactory.unquotedString("Aina Niemetz, Mathias Preiner, and contributors");
		} else if (Utils.VERSION.equals(key)) {
			lit = smtConfig.exprFactory.unquotedString("0.9.1");
		} else if (Utils.NAME.equals(key)) {
			lit = smtConfig.exprFactory.unquotedString("Bitwuzla");
		} else {
			return smtConfig.responseFactory.unsupported();
		}
		IAttribute<?> attr = smtConfig.exprFactory.attribute(key,lit);
		return smtConfig.responseFactory.get_info_response(attr);
	}

	/** Genuinely unsupported by Bitwuzla at the protocol level (see class comment point
	 *  1), regardless of whether :produce-proofs is enabled -- forwarding would kill the
	 *  process, so this is answered locally instead of going through AbstractSolver's
	 *  default (which forwards after its own precondition checks pass). */
	@Override
	public IResponse get_proof() {
		return smtConfig.responseFactory.unsupported();
	}

	/** Genuinely unsupported by Bitwuzla at the protocol level -- see {@link #get_proof()}. */
	@Override
	public IResponse get_assignment() {
		return smtConfig.responseFactory.unsupported();
	}

}
