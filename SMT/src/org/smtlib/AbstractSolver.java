/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.StringWriter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.smtlib.ICommand.*;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.SMT.Configuration;
import org.smtlib.sexpr.Parser;


/** This class implements the operations of the org.smtlib.ISolver interface that map
 *  directly onto a single translated command sent to the solver process, with the
 *  expected response of a fully SMT-LIB compliant solver (a flat success/error/sat/unsat/
 *  unknown/unsupported, or a bare value/attribute-pair for get-option/get-info): the
 *  command is translated with {@link #translate(INode)} and sent via {@link
 *  #sendCommand(ICommand)}. get_assertions/get_value/get_assignment/get_unsat_core/
 *  get_unsat_assumptions additionally reparse a non-flat response as the structured list
 *  they're actually specified to return (a {@code (term value)} pair list, a name list,
 *  etc. — see {@link org.smtlib.sexpr.Parser#parseValueList()} and its siblings), since
 *  {@link #parseResponse(String)}'s generic parse only handles flat outcomes and just
 *  returns a raw s-expression for anything else. A subclass whose target solver deviates
 *  from strict SMT-LIB concrete syntax or response format overrides {@link
 *  #translate(INode)} and/or {@link #parseResponse(String)}; a subclass whose target
 *  solver deviates in some other way overrides the individual ISolver method itself,
 *  same as before.
 *  <p>
 *  Two operations still throw UnsupportedOperationException, because AbstractSolver has
 *  no generic way to provide them: {@link #start()} and {@link #exit()} manage the
 *  solver process's lifecycle (constructing it, choosing a command line, deciding
 *  whether/how to wait for a reply before killing it).
 *  <p>
 *  Thus this class can still be used as a base class for a solver adapter class that
 *  wants the convenience of not having to implement every operation at once (remove
 *  AbstractSolver as a base class and retain ISolver as an interface to check that all
 *  ISolver methods are indeed present in the derived class), while getting working
 *  default behavior for the operations that don't need solver-specific handling.
 *
 * @author David Cok
 *
 */
public class AbstractSolver implements ISolver {

	protected static boolean isWindows = System.getProperty("os.name").contains("Wind");
	protected static boolean isMac = System.getProperty("os.name").contains("Mac");

	final protected IKeyword printSuccess;

	protected boolean printSuccessResponse = true;

	/** The object that interacts with external processes */
	protected SolverProcess solverProcess;

	/** SMT configuration — set by each concrete subclass constructor. */
	protected SMT.Configuration smtConfig;

	/** Map that keeps current values of options. */
	protected Map<String, IAttributeValue> options = new HashMap<String, IAttributeValue>();

	/** The result of the most recent check-sat or check-sat-assuming, or null if none has
	 *  been issued since the last state-changing command. */
	protected /*@Nullable*/ IResponse checkSatStatus = null;

	@Override
	public String solverName() {
	    return getClass().toString().substring(6);
	}
	
	@Override
	public void forceExit() {
		if (solverProcess != null) solverProcess.exit();
	}


	public AbstractSolver() {
		try {
			SMT.Configuration c = new SMT.Configuration();
			printSuccess = new Parser(c,c.smtFactory.createSource(":print-success",null)).parseKeyword();
		} catch (Exception e) {
			throw new RuntimeException("Failed to create an AbstractSolver: " + e);
		}
	}
	
	public IResponse successOrEmpty(SMT.Configuration smtConfig) {
		return smtConfig.nosuccess ? smtConfig.responseFactory.empty() : smtConfig.responseFactory.success();
	}

	
	public IResponse checkPrintSuccess(SMT.Configuration smtConfig,IKeyword key, IAttributeValue value) {
		if (key.equals(printSuccess)) {
			smtConfig.nosuccess = !value.toString().equals("true");
			return successOrEmpty(smtConfig);
		}
		return null;
	}

	/** Translates an in-memory node into the text sent to the solver process. The base
	 *  behavior assumes the solver is fully SMT-LIB compliant, so it is exactly what the
	 *  default printer produces. Override in a subclass whose target solver deviates from
	 *  strict SMT-LIB concrete syntax. */
	protected String translate(INode sexpr) throws IVisitor.VisitorException {
		StringWriter sw = new StringWriter();
		org.smtlib.sexpr.Printer.write(sw, sexpr);
		return sw.toString();
	}

	/** Parses the solver's raw response text. The base behavior assumes the response is
	 *  exactly standard SMT-LIB concrete syntax: success/sat/unsat/unknown/unsupported/
	 *  true/false, an {@code (error "...")} s-expression, a bare value (get-option), or a
	 *  single {@code (:keyword value)} attribute pair (get-info). It does not build the
	 *  richer structured IResponse subtypes that get_value/get_model/get_proof/
	 *  get_assertions/get_unsat_core/get_unsat_assumptions/get_assignment need, nor does it
	 *  correct for any real solver's non-compliant quirks (e.g. legacy bit-vector literal
	 *  syntax) — override in a subclass whose target solver needs either. */
	protected IResponse parseResponse(String response) {
		try {
			return new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseResponse(response);
		} catch (IParser.ParserException e) {
			return smtConfig.responseFactory.error("ParserException while parsing response: " + response + " " + e);
		}
	}

	/** Translates the given command and sends it to the solver process, returning the
	 *  parsed response. This is the mechanism behind the default implementations below;
	 *  a subclass may also call it directly to send a command built some other way. */
	protected IResponse sendCommand(ICommand cmd) {
		String translatedCmd = null;
		try {
			translatedCmd = translate(cmd);
			return parseResponse(solverProcess.sendAndListen(translatedCmd, "\n"));
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + translatedCmd + " " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + translatedCmd + " " + e);
		}
	}

	/** @see org.smtlib.ISolver#start() */
	@Override
	public IResponse start() {
		throw new UnsupportedOperationException("AbstractSolver.start");
	}

	/** @see org.smtlib.ISolver#exit() */
	@Override
	public IResponse exit() {
		throw new UnsupportedOperationException("AbstractSolver.exit");
	}
	

	@Override
	public IResponse echo(IStringLiteral arg) {
		return sendCommand(smtConfig.commandFactory.echo(arg));
	}

	@Override public void comment(String comment) {
		// No action
	}

	/** @see org.smtlib.ISolver#set_logic(String,IPos) */
	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		checkSatStatus = null;
		return sendCommand(smtConfig.commandFactory.set_logic(smtConfig.exprFactory.symbol(logicName)));
	}

	/** @see org.smtlib.ISolver#reset() */
	@Override
	public IResponse reset() {
		checkSatStatus = null;
		return sendCommand(smtConfig.commandFactory.reset());
	}

	/** @see org.smtlib.ISolver#reset_assertions() */
	@Override
	public IResponse reset_assertions() {
		checkSatStatus = null;
		return sendCommand(smtConfig.commandFactory.reset_assertions());
	}

	/** @see org.smtlib.ISolver#push(int) */
	@Override
	public IResponse push(int number) {
		checkSatStatus = null;
		return sendCommand(smtConfig.commandFactory.push(smtConfig.exprFactory.numeral(number)));
	}

	/** @see org.smtlib.ISolver#pop(int) */
	@Override
	public IResponse pop(int number) {
		checkSatStatus = null;
		return sendCommand(smtConfig.commandFactory.pop(smtConfig.exprFactory.numeral(number)));
	}

	/** @see org.smtlib.ISolver#assertExpr(IExpr) */
	@Override
	public IResponse assertExpr(IExpr sexpr) {
		checkSatStatus = null;
		return sendCommand(smtConfig.commandFactory.assertCommand(sexpr));
	}

	/** @see org.smtlib.ISolver#check_sat()*/
	@Override
	public IResponse check_sat() {
		checkSatStatus = sendCommand(smtConfig.commandFactory.check_sat());
		return checkSatStatus;
	}

	/** @see org.smtlib.ISolver#check_sat_assuming(IExpr...)*/
	@Override
	public IResponse check_sat_assuming(IExpr ... exprs) {
		checkSatStatus = sendCommand(smtConfig.commandFactory.check_sat_assuming(java.util.Arrays.asList(exprs)));
		return checkSatStatus;
	}

    /** @see org.smtlib.ISolver#define_const(ICommand.Idefine_const)  */
    @Override
    public IResponse define_const(Idefine_const cmd) {
        return define_fun(cmd);
    }

    /** @see org.smtlib.ISolver#define_fun(ICommand.Idefine_fun)  */
    @Override
    public IResponse define_fun(Idefine_fun cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

    /** @see org.smtlib.ISolver#define_fun_rec(ICommand.Idefine_fun_rec)  */
    @Override
    public IResponse define_fun_rec(Idefine_fun_rec cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

    /** @see org.smtlib.ISolver#define_funs_rec(ICommand.Idefine_funs_rec)  */
    @Override
    public IResponse define_funs_rec(Idefine_funs_rec cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

	/** @see org.smtlib.ISolver#declare_const(ICommand.Ideclare_const)  */
	@Override
	public IResponse declare_const(Ideclare_const cmd) {
		// declare-const is syntactic sugar for declare-fun with an empty argument list
		return declare_fun(smtConfig.commandFactory.declare_fun(
				cmd.symbol(), new java.util.ArrayList<>(), cmd.resultSort()));
	}

	/** @see org.smtlib.ISolver#declare_fun(ICommand.Ideclare_fun)  */
	@Override
	public IResponse declare_fun(Ideclare_fun cmd) {
		checkSatStatus = null;
		return sendCommand(cmd);
	}

	/** @see org.smtlib.ISolver#define_sort(ICommand.Idefine_sort)  */
	@Override
	public IResponse define_sort(Idefine_sort cmd){
		checkSatStatus = null;
		return sendCommand(cmd);
	}

    /** @see org.smtlib.ISolver#declare_sort(ICommand.Ideclare_sort)  */
    @Override
    public IResponse declare_sort(Ideclare_sort cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

    /** @see org.smtlib.ISolver#declare_sort_parameter(ICommand.Ideclare_sort_parameter)  */
    @Override
    public IResponse declare_sort_parameter(Ideclare_sort_parameter cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }

	/** @see org.smtlib.ISolver#set_option(IExpr.IKeyword,IExpr.IAttributeValue)  */
	@Override
	public IResponse set_option(IKeyword key, IAttributeValue value) {
		String option = key.value();
		if (Utils.REGULAR_OUTPUT_CHANNEL.equals(option)) {
			String name = (value instanceof IStringLiteral) ? ((IStringLiteral)value).value() : Utils.STDOUT;
			if (name.equals(Utils.STDOUT)) {
				smtConfig.log.out = smtConfig.stdout;
			} else if (name.equals(Utils.STDERR)) {
				smtConfig.log.out = smtConfig.stderr;
			} else {
				try {
					smtConfig.log.out = new PrintStream(new FileOutputStream(name, true));
				} catch (IOException e) {
					return smtConfig.responseFactory.error("Failed to open regular output: " + e.getMessage(), value.pos());
				}
			}
			options.put(option, value);
			return successOrEmpty(smtConfig);
		}
		if (Utils.DIAGNOSTIC_OUTPUT_CHANNEL.equals(option)) {
			String name = (value instanceof IStringLiteral) ? ((IStringLiteral)value).value() : Utils.STDERR;
			if (name.equals(Utils.STDOUT)) {
				smtConfig.log.diag = smtConfig.stdout;
			} else if (name.equals(Utils.STDERR)) {
				smtConfig.log.diag = smtConfig.stderr;
			} else {
				try {
					smtConfig.log.diag = new PrintStream(new FileOutputStream(name, true));
				} catch (IOException e) {
					return smtConfig.responseFactory.error("Failed to open diagnostic output: " + e.getMessage(), value.pos());
				}
			}
			options.put(option, value);
			return successOrEmpty(smtConfig);
		}
		return set_option_impl(key, value);
	}

	/** Override in subclasses to handle solver-specific options. Channel options are handled by set_option and never reach here. */
	protected IResponse set_option_impl(IKeyword key, IAttributeValue value) {
		return sendCommand(smtConfig.commandFactory.set_option(key, value));
	}

	/** @see org.smtlib.ISolver#set_info(IExpr.IKeyword, IExpr.IAttributeValue)  */
	@Override
	public IResponse set_info(IKeyword key, IAttributeValue value){
		return sendCommand(smtConfig.commandFactory.set_info(key, value));
	}

	/** Returns an error response if the given option has not been enabled (per
	 *  {@link #get_option(IKeyword)}), else null. */
	protected /*@Nullable*/ IResponse requireOptionEnabled(String commandName, String option) {
		if (!Utils.TRUE.equals(get_option(smtConfig.exprFactory.keyword(option)))) {
			return smtConfig.responseFactory.error("The " + commandName + " command is only valid if " + option + " has been enabled");
		}
		return null;
	}

	/** Returns an error response unless {@link #checkSatStatus} is sat or unknown, else null. */
	protected /*@Nullable*/ IResponse requireSatOrUnknown(String commandName) {
		if (!smtConfig.responseFactory.sat().equals(checkSatStatus) && !smtConfig.responseFactory.unknown().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("The " + commandName + " command is only valid immediately after check-sat returned sat or unknown");
		}
		return null;
	}

	/** Returns an error response unless {@link #checkSatStatus} is unsat, else null. */
	protected /*@Nullable*/ IResponse requireUnsat(String commandName, String afterWhat) {
		if (!smtConfig.responseFactory.unsat().equals(checkSatStatus)) {
			return smtConfig.responseFactory.error("The " + commandName + " command is only valid immediately after " + afterWhat + " returned unsat");
		}
		return null;
	}

	/** True if the given raw response text is a flat outcome (empty/success/unsupported/an
	 *  {@code (error ...)} s-expression) rather than a structured list — used by the
	 *  get_assertions/get_value/get_assignment/get_unsat_core/get_unsat_assumptions
	 *  defaults below to decide whether to delegate to {@link #parseResponse(String)} or
	 *  reparse the response as the structured list they actually expect. */
	protected boolean isFlatResponse(String response) {
		String r = response.trim();
		return r.isEmpty() || r.equals("success") || r.equals("unsupported") || r.startsWith("(error");
	}

	/** @see org.smtlib.ISolver#get_assertions() */
	@Override
	public IResponse get_assertions(){
		String key = smtConfig.atLeastVersion(SMT.Configuration.SMTLIB.V25) ? Utils.PRODUCE_ASSERTIONS : Utils.INTERACTIVE_MODE;
		IResponse err = requireOptionEnabled("get-assertions", key);
		if (err != null) return err;
		String response = null;
		try {
			// A single read may not capture a multi-line response, so keep reading
			// (paren-balance tracked across all reads so far) until it's complete.
			String cmdText = translate(smtConfig.commandFactory.get_assertions());
			StringBuilder sb = new StringBuilder();
			String s;
			int parens = 0;
			do {
				s = solverProcess.sendAndListen(cmdText, "\n");
				int p = -1;
				while ((p = s.indexOf('(',p+1)) != -1) parens++;
				p = -1;
				while ((p = s.indexOf(')',p+1)) != -1) parens--;
				sb.append(s.replace('\n',' ').replace("\r",""));
			} while (parens > 0);
			response = sb.toString();
			if (isFlatResponse(response)) return parseResponse(response);
			List<IExpr> exprs = new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseAssertionList();
			return smtConfig.responseFactory.get_assertions_response(exprs);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + e);
		} catch (IParser.ParserException e) {
			return smtConfig.responseFactory.error("Unexpected output from the solver: " + response);
		}
	}

	/** @see org.smtlib.ISolver#get_proof()*/
	@Override
	public IResponse get_proof(){
		IResponse err = requireOptionEnabled("get-proof", Utils.PRODUCE_PROOFS);
		if (err != null) return err;
		err = requireUnsat("get-proof", "check-sat");
		if (err != null) return err;
		return sendCommand(smtConfig.commandFactory.get_proof());
	}

	/** @see org.smtlib.ISolver#get_model()*/
	@Override
	public IResponse get_model(){
		IResponse err = requireOptionEnabled("get-model", Utils.PRODUCE_MODELS);
		if (err != null) return err;
		err = requireSatOrUnknown("get-model");
		if (err != null) return err;
		return sendCommand(smtConfig.commandFactory.get_model());
	}

    /** @see org.smtlib.ISolver#get_unsat_assumptions()*/
    @Override
    public IResponse get_unsat_assumptions(){
        IResponse err = requireOptionEnabled("get-unsat-assumptions", Utils.PRODUCE_UNSAT_ASSUMPTIONS);
        if (err != null) return err;
        err = requireUnsat("get-unsat-assumptions", "check-sat-assumptions");
        if (err != null) return err;
        String response = null;
        try {
            response = solverProcess.sendAndListen(translate(smtConfig.commandFactory.get_unsat_assumptions()), "\n");
            if (isFlatResponse(response)) return parseResponse(response);
            List<ISymbol> names = new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseSymbolList();
            return smtConfig.responseFactory.get_unsat_assumptions_response(names);
        } catch (IOException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IVisitor.VisitorException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IParser.ParserException e) {
            return smtConfig.responseFactory.error("Unexpected output from the solver: " + response);
        }
    }

    /** @see org.smtlib.ISolver#get_unsat_core()*/
    @Override
    public IResponse get_unsat_core(){
        IResponse err = requireOptionEnabled("get-unsat-core", Utils.PRODUCE_UNSAT_CORES);
        if (err != null) return err;
        err = requireUnsat("get-unsat-core", "check-sat");
        if (err != null) return err;
        String response = null;
        try {
            response = solverProcess.sendAndListen(translate(smtConfig.commandFactory.get_unsat_core()), "\n");
            if (isFlatResponse(response)) return parseResponse(response);
            List<ISymbol> names = new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseSymbolList();
            return smtConfig.responseFactory.get_unsat_core_response(names);
        } catch (IOException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IVisitor.VisitorException e) {
            return smtConfig.responseFactory.error("Error writing to solver: " + e);
        } catch (IParser.ParserException e) {
            return smtConfig.responseFactory.error("Unexpected output from the solver: " + response);
        }
    }

	/** @see org.smtlib.ISolver#get_value(IExpr... )*/
	@Override
	public IResponse get_value(IExpr... terms){
		IResponse err = requireOptionEnabled("get-value", Utils.PRODUCE_MODELS);
		if (err != null) return err;
		err = requireSatOrUnknown("get-value");
		if (err != null) return err;
		String response = null;
		try {
			response = solverProcess.sendAndListen(translate(smtConfig.commandFactory.get_value(java.util.Arrays.asList(terms))), "\n");
			if (isFlatResponse(response)) return parseResponse(response);
			List<IResponse.IPair<IExpr,IExpr>> values = new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseValueList();
			return smtConfig.responseFactory.get_value_response(values);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + e);
		} catch (IParser.ParserException e) {
			return smtConfig.responseFactory.error("Unexpected output from the solver: " + response);
		}
	}

	/** @see org.smtlib.ISolver#get_assignment()*/
	@Override
	public IResponse get_assignment(){
		IResponse err = requireOptionEnabled("get-assignment", Utils.PRODUCE_ASSIGNMENTS);
		if (err != null) return err;
		err = requireSatOrUnknown("get-assignment");
		if (err != null) return err;
		String response = null;
		try {
			response = solverProcess.sendAndListen(translate(smtConfig.commandFactory.get_assignment()), "\n");
			if (isFlatResponse(response)) return parseResponse(response);
			List<IResponse.IPair<ISymbol,Boolean>> assignments = new Parser(smtConfig, new org.smtlib.impl.Pos.Source(response, null)).parseAssignmentList();
			return smtConfig.responseFactory.get_assignment_response(assignments);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error writing to solver: " + e);
		} catch (IParser.ParserException e) {
			return smtConfig.responseFactory.error("Unexpected output from the solver: " + response);
		}
	}

	/** @see org.smtlib.ISolver#get_option(IExpr.IKeyword)*/
	@Override
	public IResponse get_option(IKeyword option){
		return sendCommand(smtConfig.commandFactory.get_option(option));
	}

	/** @see org.smtlib.ISolver#get_info(IExpr.IKeyword)*/
	@Override
	public IResponse get_info(IKeyword option){
		return sendCommand(smtConfig.commandFactory.get_info(option));
	}

	/** @see org.smtlib.ISolver#smt()*/
	@Override
	public Configuration smt() {
		return smtConfig;
	}

	/** @see org.smtlib.ISolver#checkSatStatus()*/
	@Override
	public IResponse checkSatStatus() {
		return checkSatStatus;
	}


    @Override
    public IResponse declare_datatype(Ideclare_datatype cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }


    @Override
    public IResponse declare_datatypes(Ideclare_datatypes cmd) {
        checkSatStatus = null;
        return sendCommand(cmd);
    }
}
