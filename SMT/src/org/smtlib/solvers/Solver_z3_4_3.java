/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

// Items not implemented:
//   attributed expressions
//   get-values get-assignment get-proof get-unsat-core
//   some error detection and handling

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.nio.charset.StandardCharsets;

import org.smtlib.*;
import org.smtlib.ICommand.Ideclare_const;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IParser.ParserException;
import org.smtlib.SMT.Configuration.SMTLIB;
import org.smtlib.impl.Pos;
import org.smtlib.sexpr.Printer;
import org.smtlib.Utils;

/** This class is an adapter that takes the SMT-LIB ASTs and translates them into Z3 commands */
public class Solver_z3_4_3 extends AbstractSolver implements ISolver {
	
	/** The solver's display name for diagnostic logging. A real, overridable method rather
	 *  than a field -- a field here would be hidden, not overridden, by a subclass's own
	 *  same-named field (Java fields aren't polymorphic), silently binding start()'s
	 *  reference to this class's value regardless of which subclass is actually running.
	 *  See issue #51. */
	protected String name() { return "z3-4.3"; }

	// linesOffset is inherited from AbstractSolver -- see its own doc comment there.

	/** The command-line arguments for launching the Z3 solver */
	protected String cmds[];
	// WARNING=false suppresses z3's own diagnostic WARNING messages (e.g. "unknown logic,
	// ignoring set-logic command"): confirmed directly against the real z3-4.3.1 binary
	// that these print as a bare "WARNING: ..." line with no parens at all, which fools
	// SolverProcess's paren-balance response-completion heuristic the same way
	// Solver_z3_recent's own identical WARNING=false comment already documents for that
	// adapter -- z3-4.3 never got the same fix.
	protected String cmds_win[] = new String[]{ "", "/smt2","/in","SMTLIB2_COMPLIANT=true","WARNING=false"};//,"/rs:42"};
	protected String cmds_mac[] = new String[]{ "", "-smt2","-in","SMTLIB2_COMPLIANT=true","WARNING=false"};
	protected String cmds_unix[] = new String[]{ "", "-smt2","-in","WARNING=false"};
	
	/** The parser that parses responses from the solver */
	protected org.smtlib.sexpr.Parser responseParser;
	
	/** Set to true once a set-logic command has been executed */
	protected boolean logicSet = false;
	
	/** The checkSatStatus returned by check-sat, if sufficiently recent, otherwise null */
	protected /*@Nullable*/ IResponse checkSatStatus = null;
	
	@Override
	public /*@Nullable*/IResponse checkSatStatus() { return checkSatStatus; }

	/** The number of pushes less the number of pops so far -- i.e. the real depth of the
	 *  solver's own assertion stack. 0 immediately after set_logic(), before any push (not
	 *  1: set_logic() does not itself push anything). Used to know how much to pop for
	 *  set_logic()'s relax-mode re-entry cleanup; NOT used to validate a pop count client-side
	 *  -- z3-4.3 already does that itself, with better diagnostics than this adapter could
	 *  produce (see #53), so only update this after the solver confirms a pop actually
	 *  succeeded, never unconditionally. */
	protected int pushesDepth = 0;
	
	/** Creates an instance of the Z3 solver */
	public Solver_z3_4_3(SMT.Configuration smtConfig, /*@NonNull*/ String executable) {
		this.smtConfig = smtConfig;
		if (isWindows) {
			cmds = cmds_win;
		} else if (isMac) {
			cmds = cmds_mac;
		} else {
			cmds = cmds_unix;
		}
		// -rs:N is appended for mac/unix only; the Windows build is deliberately not given a
		// seed flag (see the String[]-command constructor below for the same exclusion).
		if (smtConfig.seed != 0 && !isWindows) {
			List<String> args = new java.util.ArrayList<String>(Arrays.asList(cmds));
			args.add("-rs:" + smtConfig.seed);
			cmds = args.toArray(new String[args.size()]);
		}
		cmds[0] = executable;
		options.putAll(smtConfig.utils.defaults);
		cmds = withTimeoutArgs(cmds, smtConfig, isWindows);
		solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
		responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("",null));
	}

	/** Creates an instance of the Z3 solver */
	public Solver_z3_4_3(SMT.Configuration smtConfig, /*@NonNull*/ String[] command) {
		this.smtConfig = smtConfig;
		cmds = command;
		options.putAll(smtConfig.utils.defaults);
        // Windows is deliberately excluded -- the equivalent there would be
        // args.add("/rs:" + smtConfig.seed), which was commented out rather than used.
        if (smtConfig.seed != 0 && !isWindows) {
            List<String> args = new java.util.ArrayList<String>(Arrays.asList(cmds));
            args.add("-rs:" + smtConfig.seed);
            cmds = args.toArray(new String[args.size()]);
        }
		cmds = withTimeoutArgs(cmds, smtConfig, isWindows);
		solverProcess = new SolverProcess(cmds,"\n",smtConfig.logfile,StandardCharsets.UTF_8);
		responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source("",null));
	}

	/** Appends z3-4.3's own timeout flags for smtConfig's two jSMTLIB-level, seconds-based
	 *  timeout values, if set: {@code -t:N} (or {@code /t:N} on Windows) for the per-query
	 *  soft timeout ({@code smtConfig.timeout}), {@code -T:N}/{@code /T:N} for the whole-run
	 *  timeout ({@code smtConfig.timeoutTotal}). z3-4.3 uses seconds for both, so no unit
	 *  conversion is needed here (unlike most other adapters). */
	private static String[] withTimeoutArgs(String[] cmds, SMT.Configuration smtConfig, boolean isWindows) {
		double timeout = smtConfig.timeout;
		double timeoutTotal = smtConfig.timeoutTotal;
		if (timeout <= 0 && timeoutTotal <= 0) return cmds;
		List<String> args = new java.util.ArrayList<String>(Arrays.asList(cmds));
		if (timeout > 0) args.add(isWindows ? "/t:" + (int)timeout : "-t:" + (int)timeout);
		if (timeoutTotal > 0) args.add(isWindows ? "/T:" + (int)timeoutTotal : "-T:" + (int)timeoutTotal);
		return args.toArray(new String[args.size()]);
	}

	public IResponse sendCommand(ICommand cmd) {
		String translatedCmd = null;
		try {
			translatedCmd = translate(cmd);
			return parseResponse(solverProcess.sendAndListen(translatedCmd,"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + translatedCmd + " " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + translatedCmd + " " + e);
		}
	}
	
	public IResponse sendCommand(String cmd) {
		try {
			return parseResponse(solverProcess.sendAndListen(cmd,"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + cmd + " " + e);
		}
	}
	

	@Override
	public IResponse start() {
		try {
			solverProcess.start(false);
			// FIXME - enable the following lines when the Z3 solver supports them
//			if (smtConfig.solverVerbosity > 0) solverProcess.sendNoListen("(set-option :verbosity ",Integer.toString(smtConfig.solverVerbosity),")");
//			if (!smtConfig.batch) solverProcess.sendNoListen("(set-option :interactive-mode true)"); // FIXME - not sure we can do this - we'll lose the feedback
			// Can't turn off printing success, or we get no feedback
			solverProcess.sendAndListen("(set-option :print-success true)\n"); // Z3 4.3.0 needs this because it mistakenly has the default for :print-success as false
			linesOffset ++; 
			//if (smtConfig.nosuccess) solverProcess.sendAndListen("(set-option :print-success false)");
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Started "+name()+" ");
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}
	
	@Override
	public IResponse exit() {
		try {
			solverProcess.sendAndListen("(exit)\n");
			solverProcess.exit();
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended Z3 ");
			return successOrEmpty(smtConfig);
		} catch (SolverProcess.NoResponseException e) {
			// The response text is discarded either way (this adapter never trusted
			// z3-4.3's raw responses to begin with -- see the class-level history in
			// Solver_z3_recent's javadoc), so a silently-closed connection reaches the
			// same successOrEmpty() outcome as a normal response, not an error.
			solverProcess.exit();
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended Z3 ");
			return successOrEmpty(smtConfig);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}
	
	@Override
	public void forceExit() {
		if (solverProcess != null) solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#Ended Z3 forcibly");
	}

	// comment() is inherited unchanged from AbstractSolver, which now forwards a standalone
	// comment to any solver -- see AbstractSolver.comment() (issue #96/#97's line-counting
	// investigation established comments must reach every adapter uniformly, not just this
	// one, for line-number rewriting to correctly track the user's real script).

	/** Translates an S-expression into Z3 syntax */
	protected String translate(INode sexpr) throws IVisitor.VisitorException {
		// The z3 solver uses the standard S-expression concrete syntax, but not quite
		// so we have to use our own translator
		StringWriter sw = new StringWriter();
		sexpr.accept(new Translator(sw));
		return sw.toString();
	}
	
	// No translateSMT(INode) here -- a confirmed dead end, not just unused. It once existed
	// as a shortcut to print an entire subtree with plain standard SMT-LIB syntax, bypassing
	// Translator's Z3-specific overrides, but that doesn't compose safely: a subtree handed to
	// it wholesale might contain other nested nodes that still need Translator's own handling,
	// which plain printing would silently lose. Translator's visit(IFcnExpr) documents exactly
	// this ("we can't delegate to translateSMT because it might be a sub-expression") --
	// Translator's ordinary super.visit(e) fallback (inherited from Printer) already covers
	// "plain printing for a single node with no override" correctly; only a whole-subtree
	// bypass was ever the problem. See issue #65.

	protected IResponse parseResponse(String response) {
		try {
			Pattern oldbv = Pattern.compile("bv([0-9]+)\\[([0-9]+)\\]");
			Matcher mm = oldbv.matcher(response);
			while (mm.find()) {
				long val = Long.parseLong(mm.group(1));
				int base = Integer.parseInt(mm.group(2));
				String bits = "";
				for (int i=0; i<base; i++) { bits = ((val&1)==0 ? "0" : "1") + bits; val = val >>> 1; }
				response = response.substring(0,mm.start()) + "#b" + bits + response.substring(mm.end(),response.length());
				mm = oldbv.matcher(response);
			}
			if (isMac && response.startsWith("success")) return smtConfig.responseFactory.success(); // FIXME - this is just to avoid a problem with the Mac Z3 implementation
			if (response.contains("error")) {
				// Z3 returns an s-expr (always?)
				// FIXME - (1) the {Print} also needs {Space}; (2) err_getValueTypes.tst returns a non-error s-expr and then an error s-expr - this fails for that case
				//Pattern p = Pattern.compile("\\p{Space}*\\(\\p{Blank}*error\\p{Blank}+\"(([\\p{Space}\\p{Print}^[\\\"\\\\]]|\\\\\")*)\"\\p{Blank}*\\)\\p{Space}*");
				Pattern p = Pattern.compile("\\p{Space}*\\(\\p{Blank}*error\\p{Blank}+\"(([\\p{Print}\\p{Space}&&[^\"\\\\]]|\\\\\")*)\"\\p{Blank}*\\)");
				Matcher m = p.matcher(response);
				String concat = "";
				while (m.lookingAt()) {
					if (!concat.isEmpty()) concat = concat + "; ";
					String matched = m.group(1);
					String prefix = "line ";
					int offset = prefix.length();
					if (matched.startsWith(prefix)) {
						int k = matched.indexOf(' ',offset);
						String number = matched.substring(offset, k);
						try {
							int n = Integer.parseInt(number);
							matched = prefix + (n-linesOffset) + matched.substring(k);
						} catch (NumberFormatException e) {
							// Just continue
						}
					}
					concat = concat + matched;
					m.region(m.end(0),m.regionEnd());
				}
				if (!concat.isEmpty()) response = concat;
				return smtConfig.responseFactory.error(response);
			}
			responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source(response,null));
			return responseParser.parseResponse(response);
		} catch (ParserException e) {
			return smtConfig.responseFactory.error("ParserException while parsing response: " + response + " " + e);
		}
	}

	@Override
	public IResponse assertExpr(IExpr sexpr) {
		IResponse response;
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before an assert command is issued");
		}
		try {
			String s = solverProcess.sendAndListen("(assert ",translate(sexpr),")\n");
			response = parseResponse(s);
			checkSatStatus = null;
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Failed to assert expression: " + e + " " + sexpr);
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to assert expression: " + e + " " + sexpr);
		}
		return response;
	}
	
	@Override
	public IResponse get_assertions() {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a get-assertions command is issued");
		}
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!smtConfig.relax && !Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_ASSERTIONS)))) {
			return smtConfig.responseFactory.error("The get-assertions command is only valid if " + Utils.produceAssertionsKey(smtConfig) + " has been enabled");
		}
		try {
			StringBuilder sb = new StringBuilder();
			String s;
			int parens = 0;
			do {
				s = solverProcess.sendAndListen("(get-assertions)\n");
				int p = -1;
				while (( p = s.indexOf('(',p+1)) != -1) parens++;
				p = -1;
				while (( p = s.indexOf(')',p+1)) != -1) parens--;
				sb.append(s.replace('\n',' ').replace("\r",""));
			} while (parens > 0);
			s = sb.toString();
			org.smtlib.sexpr.Parser p = new org.smtlib.sexpr.Parser(smtConfig,new org.smtlib.impl.Pos.Source(s,null));
			List<IExpr> exprs = new LinkedList<IExpr>();
			try {
				if (p.isLP()) {
					p.parseLP();
					while (!p.isRP() && !p.isEOD()) {
						IExpr e = p.parseExpr();
						exprs.add(e);
					}
					if (p.isRP()) {
						p.parseRP();
						if (p.isEOD()) return smtConfig.responseFactory.get_assertions_response(exprs); 
					}
				}
			} catch (Exception e ) {
				// continue - fall through
			}
			return smtConfig.responseFactory.error("Unexpected output from the Z3 solver: " + s);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("IOException while reading Z3 reponse");
		}
	}
	


	@Override
	public IResponse check_sat() {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a check-sat command is issued");
		}
		checkSatStatus = sendCommand(smtConfig.commandFactory.check_sat());
		return checkSatStatus;
	}
	
	@Override
	public IResponse reset() {
		logicSet = false;
		pushesDepth = 0;
	    return sendCommand("(reset)");
	}

	/** z3-4.3 predates reset-assertions (added in SMT-LIB 2.5), and turns out to already
	 *  handle that gracefully on its own: sent the literal, unrecognized command text, its
	 *  SMT2 front-end replies with the literal token "unsupported" -- confirmed directly
	 *  against a real z3-4.3.1 binary -- rather than erroring or crashing. That's the
	 *  correct, honest answer for a solver that genuinely can't do this, so there is nothing
	 *  for the adapter to improve on here: a from-jSMTLIB pop-to-base simulation was tried
	 *  and reverted -- it silently claimed success while only partially honoring the
	 *  contract (it can only clear pushed-frame state, not declarations, and per issue #53
	 *  discussion, non-global declarations are also supposed to be cleared by
	 *  reset-assertions, which this adapter has no way to do without locally tracking every
	 *  declaration), and it desynced the linesOffset bookkeeping used to translate Z3's own
	 *  reported error positions back to the script's real line numbers, corrupting later
	 *  error messages. See issue #53. */
	@Override
	public IResponse reset_assertions() {
	    return sendCommand("(reset-assertions)");
	}

	@Override
	public IResponse pop(int number) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a pop command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A pop command called with a negative argument: " + number);
		if (number == 0) return  successOrEmpty(smtConfig);
		try {
			checkSatStatus = null;
			// Deliberately no client-side bound check against pushesDepth here: z3-4.3
			// already validates a pop count against its own real stack depth and reports a
			// precise, line/column-annotated error itself (confirmed against a real
			// z3-4.3.1 binary: "invalid pop command, argument is greater than the current
			// stack depth") -- better diagnostics than anything this adapter could produce,
			// so defer to it (see issue #53). Only update the local depth bookkeeping once
			// the solver actually accepted the pop; otherwise nothing was really popped and
			// pushesDepth must not drift from what the solver's real stack looks like.
			IResponse response = parseResponse(solverProcess.sendAndListen("(pop ",Integer.toString(number),")\n"));
			if (!response.isError()) pushesDepth -= number;
			return response;
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse push(int number) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a push command is issued");
		}
		if (number < 0) throw new SMT.InternalException("Internal bug: A push command called with a negative argument: " + number);
		checkSatStatus = null;
		if (number == 0) return smtConfig.responseFactory.success();
		try {
			pushesDepth += number;
			// Used to convert any push() error into success whenever !isWindows (issue #53),
			// on the strength of a comment claiming the problem was Linux-only -- but the
			// condition covered macOS too, and a diagnostic logged unconditionally across a
			// full 5-platform CI run (thousands of tests, including plenty of push/pop
			// coverage) never once found push() returning an error on ANY platform. With no
			// reproducible case anywhere to justify masking it, and no evidence for the
			// Linux-only claim either, the honest, platform-independent behavior is to
			// return exactly what the solver said, uniformly.
			return parseResponse(solverProcess.sendAndListen("(push ",Integer.toString(number),")\n"));
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		// FIXME - discriminate among logics
		
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("#set-logic " + logicName);
		if (logicSet) {
			if (!smtConfig.relax) return smtConfig.responseFactory.error("Logic is already set");
			pop(pushesDepth); // pop back to the base frame -- pushesDepth is 0 again afterward
		}
		logicSet = true;
		if (logicName.equals("ALL")) {
			// z3-4.3 has no "ALL" logic to declare, so this line is never actually sent --
			// unlike every other logic name, which the else-branch below sends as a real,
			// counted line. That's one fewer real script line reflected in what z3 counts, so
			// linesOffset must be decremented to compensate (see issue #97): otherwise every
			// line-numbered error later in the script under-reports by one relative to the
			// user's actual source.
			linesOffset--;
			return smtConfig.responseFactory.success();
		} else try {
			return parseResponse(solverProcess.sendAndListen("(set-logic ",logicName,")\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e,pos);
		}
	}

	@Override
	protected IResponse set_option_impl(IKeyword key, IAttributeValue value) {
		String option = key.value();
		if (Utils.PRINT_SUCCESS.equals(option)) {
			if (!(Utils.TRUE.equals(value) || Utils.FALSE.equals(value))) {
				return smtConfig.responseFactory.error("The value of the " + option + " option must be 'true' or 'false'");
			}
		}
		if (logicSet && (Utils.INTERACTIVE_MODE.equals(option)||Utils.PRODUCE_ASSERTIONS.equals(option))) {
			return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
		}
		if (Utils.PRODUCE_ASSIGNMENTS.equals(option) ||
				Utils.PRODUCE_PROOFS.equals(option) ||
				Utils.PRODUCE_UNSAT_CORES.equals(option)) {
			if (logicSet) return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
			return smtConfig.responseFactory.unsupported();
		}
		if (Utils.PRODUCE_MODELS.equals(option)) {
			if (logicSet) return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
		}
		if (Utils.VERBOSITY.equals(option)) {
			IAttributeValue v = options.get(option);
			smtConfig.verbose = (v instanceof INumeral) ? ((INumeral)v).intValue() : 0;
		}
		// Save the options on our side as well
		options.put(Utils.INTERACTIVE_MODE.equals(option) && !smtConfig.isVersion(SMTLIB.V20) ? Utils.PRODUCE_ASSERTIONS : option,value);
		IResponse r = checkPrintSuccess(smtConfig,key,value);
		if (r != null) return r;

		try {
			solverProcess.sendAndListen("(set-option ",option," ",value.toString(),")\n");// FIXME - detect errors
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}

		return successOrEmpty(smtConfig);
	}

	@Override
	public IResponse get_option(IKeyword key) { // FIXME - use the solver?
		String option = key.value();
		IAttributeValue value = options.get(Utils.INTERACTIVE_MODE.equals(option) && !smtConfig.isVersion(SMTLIB.V20)? Utils.PRODUCE_ASSERTIONS : option);
		if (value == null) return smtConfig.responseFactory.unsupported();
		return value;
	}

	@Override
	public IResponse get_info(IKeyword key) {
		String cmd = "(get-info " + key + ")";
		try {
			String response = solverProcess.sendAndListen(cmd, "\n");
			if (smtConfig.testing) response = normalizeForTesting(response);
			return parseResponse(response);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + cmd + " " + e);
		}
	}
	
	@Override
	public IResponse set_info(IKeyword key, IAttributeValue value) {
		if (Utils.infoKeywords.contains(key)) {
			return smtConfig.responseFactory.error("Setting the value of a pre-defined keyword is not permitted: "+
					smtConfig.defaultPrinter.toString(key),key.pos());
		}
		return sendCommand(new org.smtlib.command.C_set_info(key,value));
	}

	@Override
	public IResponse echo(IStringLiteral arg) {
		return arg;
	}

	@Override
	public IResponse get_model() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS)))) {
			return smtConfig.responseFactory.error("The get-model command is only valid if :produce-models has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.sat() && checkSatStatus != smtConfig.responseFactory.unknown()) {
			return smtConfig.responseFactory.error("The get-model command is only valid immediately after check-sat returned sat or unknown");
		}
		try {
			return parseResponse(solverProcess.sendAndListen("(get-model)\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse declare_const(Ideclare_const cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-const command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse declare_fun(Ideclare_fun cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-fun command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));

		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a define-fun command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse declare_sort(Ideclare_sort cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a declare-sort command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override
	public IResponse define_sort(Idefine_sort cmd) {
		if (!logicSet) {
			return smtConfig.responseFactory.error("The logic must be set before a define-sort command is issued");
		}
		try {
			checkSatStatus = null;
			return parseResponse(solverProcess.sendAndListen(translate(cmd),"\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}
	
	@Override 
	public IResponse get_proof() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_PROOFS)))) {
			return smtConfig.responseFactory.error("The get-proof command is only valid if :produce-proofs has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.unsat()) {
			return smtConfig.responseFactory.error("The get-proof command is only valid immediately after check-sat returned unsat");
		}
		try {
			return parseResponse(solverProcess.sendAndListen("(get-proof)\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override 
	public IResponse get_unsat_core() {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_UNSAT_CORES)))) {
			return smtConfig.responseFactory.error("The get-unsat-core command is only valid if :produce-unsat-cores has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.unsat()) {
			return smtConfig.responseFactory.error("The get-unsat-core command is only valid immediately after check-sat returned unsat");
		}
		try {
			return parseResponse(solverProcess.sendAndListen("(get-unsat-core)\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override 
	public IResponse get_assignment() {
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_ASSIGNMENTS)))) {
			return smtConfig.responseFactory.error("The get-assignment command is only valid if :produce-assignments has been enabled");
		}
		if (checkSatStatus != smtConfig.responseFactory.sat() && checkSatStatus != smtConfig.responseFactory.unknown()) {
			return smtConfig.responseFactory.error("The get-assignment command is only valid immediately after check-sat returned sat or unknown");
		}
		try {
			return parseResponse(solverProcess.sendAndListen("(get-assignment)\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	@Override 
	public IResponse get_value(IExpr... terms) {
		// FIXME - do we really want to call get-option here? it involves going to the solver?
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(Utils.PRODUCE_MODELS)))) {
			return smtConfig.responseFactory.error("The get-value command is only valid if :produce-models has been enabled");
		}
		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("A get-value command is valid only after check-sat has returned sat or unknown");
		}
		try {
			solverProcess.sendNoListen("(get-value (");
			for (IExpr e: terms) {
				solverProcess.sendNoListen(" ",translate(e));
			}
			String r = solverProcess.sendAndListen("))\n");
			IResponse response = parseResponse(r);
//			if (response instanceof ISeq) {
//				List<ISexpr> valueslist = new LinkedList<ISexpr>();
//				Iterator<ISexpr> iter = ((ISeq)response).sexprs().iterator();
//				for (IExpr e: terms) {
//					if (!iter.hasNext()) break;
//					List<ISexpr> values = new LinkedList<ISexpr>();
//					values.add(new Sexpr.Expr(e));
//					values.add(iter.next());
//					valueslist.add(new Sexpr.Seq(values));
//				}	
//				return new Sexpr.Seq(valueslist);
//			}
			return response;
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to Z3 solver: " + e);
		}
	}

	public class Translator extends Printer {

		public Translator(Writer w) { super(Solver_z3_4_3.this.smtConfig, w); }

		@Override
		public Void visit(IFcnExpr e) throws IVisitor.VisitorException {
			// Only - for >=2 args is not correctly done, but we can't delegate to translateSMT because it might be a sub-expression.
			Iterator<IExpr> iter = e.args().iterator();
			if (!iter.hasNext()) throw new VisitorException("Did not expect an empty argument list",e.pos());
			IQualifiedIdentifier fcn = e.head();
			int length = e.args().size();
			if (length > 2 && (fcn instanceof IIdentifier) && fcn.toString().equals("-")) {
				leftassoc(fcn.toString(),length,iter);
			} else {
				super.visit(e);
			}
			return null;
		}

		//@ requires iter.hasNext();
		//@ requires length > 0;
		protected <T extends IExpr> void leftassoc(String fcnname, int length, Iterator<T> iter ) throws IVisitor.VisitorException {
			if (length == 1) {
				iter.next().accept(this);
			} else {
				try {
					w.append("(");
					w.append(fcnname);
					w.append(" ");
					leftassoc(fcnname,length-1,iter);
					w.append(" ");
					iter.next().accept(this);
					w.append(")");
				} catch (IOException ex) {
					throw new IVisitor.VisitorException(ex,null); // FIXME - null ?
				}
			}
		}

		//@ requires iter.hasNext();
		protected <T extends IExpr> void rightassoc(String fcnname, Iterator<T> iter ) throws IVisitor.VisitorException {
			T n = iter.next();
			if (!iter.hasNext()) {
				n.accept(this);
			} else {
				try {
					w.append("(");
					w.append(fcnname);
					w.append(" ");
					n.accept(this);
					w.append(" ");
					rightassoc(fcnname,iter);
					w.append(")");
				} catch (IOException ex) {
					throw new IVisitor.VisitorException(ex,null); // FIXME - null ?
				}
			}
		}

		
		//@ requires iter.hasNext();
		//@ requires length > 0;
		protected <T extends INode> void chainable(String fcnname, Iterator<T> iter ) throws IVisitor.VisitorException {
			try {
				w.append("(and ");
				T left = iter.next();
				while (iter.hasNext()) {
					w.append("(");
					w.append(fcnname);
					w.append(" ");
					left.accept(this);
					w.append(" ");
					(left=iter.next()).accept(this);
					w.append(")");
				}
				w.append(")");
			} catch (IOException ex) {
				throw new IVisitor.VisitorException(ex,null); // FIXME - null ?
			}
		}
	}
}
