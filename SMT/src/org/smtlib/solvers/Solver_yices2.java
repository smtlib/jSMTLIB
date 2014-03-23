/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.smtlib.*;
import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.ICommand.Ideclare_sort;
import org.smtlib.ICommand.Idefine_fun;
import org.smtlib.ICommand.Idefine_sort;
import org.smtlib.IExpr.IAsIdentifier;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IAttributeValue;
import org.smtlib.IExpr.IAttributedExpr;
import org.smtlib.IExpr.IBinaryLiteral;
import org.smtlib.IExpr.IBinding;
import org.smtlib.IExpr.IDecimal;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IError;
import org.smtlib.IExpr.IExists;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IForall;
import org.smtlib.IExpr.IHexLiteral;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ILet;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse.IPair;
import org.smtlib.impl.Pos;
import org.smtlib.impl.Response;
import org.smtlib.impl.SMTExpr.ParameterizedIdentifier;
import org.smtlib.sexpr.ISexpr;

// FIXME - in some commands, like assert, push, pop, the effect in solver_test happens even if the effect in the 
// solver itself causes an error, putting the two out of synch; also, push and pop can happen partially
/** This class is the adapter for the Yices SMT solver */
public class Solver_yices2 extends Solver_test implements ISolver {
	/** This holds the command-line arguments used to launch the solver;
	 * the path to the executable is inserted in cmds[0]. */
	String cmds[] = new String[]{"","--mode=interactive"};
	
	/** Holds the driver for external processes */
	private SolverProcess solverProcess;
	
	/** The string that indicates an Error in the solver reply */
	static public final String errorIndication = "Error";

	/** Records the values of options */
	{ 
		options.putAll(Utils.defaults);
	}
	
	/** Creates but does not start a solver instance */
	public Solver_yices2(SMT.Configuration smtConfig, String executable) {
		super(smtConfig,"");
		cmds[0] = executable;
		solverProcess = new SolverProcess(cmds,"yices> ",smtConfig.logfile) {
			@Override
			public String listen() throws IOException {
				// FIXME - need to put the two reads in parallel, otherwise one might block on a full buffer, preventing the other from completing
				String err = listenThru(errors,endMarker);
				String out = listenThru(fromProcess,null);
				if (err.endsWith(endMarker)) err = err.substring(0,err.length()-endMarker.length());
				if (log != null) {
					if (!out.isEmpty()) { log.write(";;OUT: "); log.write(out); log.write(eol); } // input usually ends with a prompt and no line terminator
					if (!err.isEmpty()) { log.write(";;ERR: "); log.write(err); } // input usually ends with a line terminator, we think
				}
				return err.isEmpty() ? out : err;
			}
		};
	}
	
	@Override
	public IResponse start() {
		super.start();
		try {
			solverProcess.start(true);
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Started yices2 " + (solverProcess!=null));
//			solverProcess.sendAndListen("(define mod :: (-> int int int))\n");
//			solverProcess.sendAndListen("(define div :: (-> int int int))\n");
			
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}
	
	protected /*@Nullable*/ IResponse send(IPos pos, String... solverCmds) {
		try {
			for (String s: solverCmds) solverProcess.sendNoListen(s);
			String response = solverProcess.sendAndListen("\n");
			if (response.contains(errorIndication) || response.contains("does not support quantifiers")) {
				return smtConfig.responseFactory.error(response,pos);
			}
			return null;
		} catch (IOException e) {
			return smtConfig.responseFactory.error(e.getMessage(),pos);
		}
	}

	// FIXME - are we capturing errors from the solver?
	
	@Override
	public IResponse exit() {
		IResponse r = send(null,"(exit)");
		if (r != null) return r;
		solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("Ended yices2 ");
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse assertExpr(IExpr sexpr) {
		try {
			IResponse status = super.assertExpr(sexpr);
			if (!status.isOK()) return status;

			IResponse response = send(sexpr.pos(),"(assert ",translate(sexpr)," )");
			if (response != null) return response;
			return status;
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Yices assert command failed: " + e.getMessage());
		}

	}

	@Override
	public IResponse check_sat() {
		IResponse res = super.check_sat();
		if (res.isError()) return res;

		try {
			String s = solverProcess.sendAndListen("(check)\r\n");
			if (s.contains(errorIndication)) {
				return smtConfig.responseFactory.error(s);
			}
			//System.out.println("HEARD: " + s);
			if (s.contains("unsat")) res = smtConfig.responseFactory.unsat();
			else if (s.contains("sat")) res = smtConfig.responseFactory.sat();
			else res = smtConfig.responseFactory.unknown();
			checkSatStatus = res;
		} catch (IOException e) {
			res = smtConfig.responseFactory.error("Failed to check-sat");
		}
		return res;
	}

	@Override
	public IResponse pop(int number) {
		IResponse status = super.pop(number);
		if (status.isError()) return status;
		while (number-- > 0) {
			IResponse response = send(null,"(pop)");
			if (response != null) return response;
		}
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse push(int number) {
		IResponse status = super.push(number);
		if (status.isError()) return status;
		while (number-- > 0) {
			IResponse response = send(null,"(push)");
			if (response != null) return response;
		}
		return smtConfig.responseFactory.success();
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		boolean lSet = logicSet;
		IResponse status = super.set_logic(logicName,pos);
		if (!status.isOK()) return status;

		// FIXME - discrimninate among logics

		if (lSet) {
			if (!smtConfig.relax) return smtConfig.responseFactory.error("Logic is already set");
			IResponse response = send(pos,"(reset)");
			if (response != null) return response;
		}
		return status;
	}

	@Override
	public IResponse set_option(IKeyword key, IAttributeValue value) {
		String option = key.value();
		if (Utils.PRINT_SUCCESS.equals(option)) {
			if (!(Utils.TRUE.equals(value) || Utils.FALSE.equals(value))) {
				return smtConfig.responseFactory.error("The value of the " + option + " option must be 'true' or 'false'");
			}
			// FIXME - improve the following line
			((Response.Factory)smtConfig.responseFactory).printSuccess = !Utils.FALSE.equals(value);
		}
		if (Utils.INTERACTIVE_MODE.equals(option) || 
				Utils.PRODUCE_MODELS.equals(option) ||
				Utils.PRODUCE_UNSAT_CORES.equals(option)) {
			if (logicSet) return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
		} else if (Utils.PRODUCE_ASSIGNMENTS.equals(option) || 
				Utils.PRODUCE_PROOFS.equals(option)) {
			if (logicSet) return smtConfig.responseFactory.error("The value of the " + option + " option must be set before the set-logic command");
			return smtConfig.responseFactory.unsupported();
		}
		if (Utils.VERBOSITY.equals(option)) {
			IAttributeValue v = options.get(option);
			smtConfig.verbose = (v instanceof INumeral) ? ((INumeral)v).intValue() : 0;
		} else if (Utils.DIAGNOSTIC_OUTPUT_CHANNEL.equals(option)) {
			// Actually, v should never be anything but IStringLiteral - that should
			// be checked during parsing
			String name = (value instanceof IStringLiteral)? ((IStringLiteral)value).value() : "stderr";
			if (name.equals("stdout")) {
				smtConfig.log.diag = System.out;
			} else if (name.equals("stderr")) {
				smtConfig.log.diag = System.err;
			} else {
				try {
					FileOutputStream f = new FileOutputStream(name,true); // append
					smtConfig.log.diag = new PrintStream(f);
				} catch (java.io.IOException e) {
					return smtConfig.responseFactory.error("Failed to open or write to the diagnostic output " + e.getMessage(),value.pos());
				}
			}
		} else if (Utils.REGULAR_OUTPUT_CHANNEL.equals(option)) {
			// Actually, v should never be anything but IStringLiteral - that should
			// be checked during parsing
			String name = (value instanceof IStringLiteral)?((IStringLiteral)value).value() : "stdout";
			if (name.equals("stdout")) {
				smtConfig.log.out = System.out;
			} else if (name.equals("stderr")) {
				smtConfig.log.out = System.err;
			} else {
				try {
					FileOutputStream f = new FileOutputStream(name,true); // append
					smtConfig.log.out = new PrintStream(f);
				} catch (java.io.IOException e) {
					return smtConfig.responseFactory.error("Failed to open or write to the regular output " + e.getMessage(),value.pos());
				}
			}
		}
		options.put(option,value);
		return smtConfig.responseFactory.success();
	}

//	@Override
//	public IResponse get_option(IKeyword key) {
//		String option = key.value();
//		IAttributeValue value = options.get(option);
//		if (value == null) return smtConfig.responseFactory.unsupported();
//		return value;
//	}

	@Override
	public IResponse get_info(IKeyword key) {
		String option = key.value();
		IAttributeValue lit;
		if (":error-behavior".equals(option)) {
			lit = smtConfig.exprFactory.symbol(Utils.CONTINUED_EXECUTION); // FIXME
		} else if (":status".equals(option)) {
			return checkSatStatus==null ? smtConfig.responseFactory.unsupported() : checkSatStatus; 
		} else if (":all-statistics".equals(option)) {
			return smtConfig.responseFactory.unsupported(); // FIXME
		} else if (":reason-unknown".equals(option)) {
			return smtConfig.responseFactory.unsupported(); // FIXME
		} else if (":authors".equals(option)) {
			lit = smtConfig.exprFactory.unquotedString("SRI");
		} else if (":version".equals(option)) {
			lit = smtConfig.exprFactory.unquotedString("2.1");
		} else if (":name".equals(option)) {
			lit = smtConfig.exprFactory.unquotedString("yices2");
		} else {
			return smtConfig.responseFactory.unsupported();
		}
		IAttribute<?> attr = smtConfig.exprFactory.attribute(key,lit);
		return smtConfig.responseFactory.get_info_response(attr);
	}
	
	@Override
	public IResponse declare_fun(Ideclare_fun cmd) {
		try {
			IResponse status = super.declare_fun(cmd);
			if (!status.isOK()) return status;

			String name = translate(cmd.symbol());
			String yicescmd;
			if (cmd.argSorts().size() == 0) {
				yicescmd = "(define " + name + "::" + translate(cmd.resultSort()) + ")";
			} else {
				yicescmd = "(define " + name + "::(->";
				for (ISort s: cmd.argSorts()) {
					yicescmd = yicescmd + " " + translate(s);
				}
				yicescmd = yicescmd + " " + translate(cmd.resultSort()) + "))";
				
			}
			IResponse response = send(null,yicescmd);
			if (response != null) return response;
			return status;
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("declare-fun command failed: " + e.getMessage());
		}
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		try {
			IResponse status = super.define_fun(cmd);
			if (!status.isOK()) return status;
			
			String name = translate(cmd.symbol());
			StringBuilder yicescmd = new StringBuilder();;
			if (cmd.parameters().size() == 0) {
				yicescmd.append("(define " + name + "::" + translate(cmd.resultSort()) + " " 
								+ translate(cmd.expression()));
			} else {
				yicescmd.append("(define " + name + "::(->");
				for (IDeclaration d: cmd.parameters()) {
					yicescmd.append(" " + translate(d.sort()));
				}
				yicescmd.append(" " + translate(cmd.resultSort()) + ") ");
				yicescmd.append("(lambda (");
				for (IDeclaration d: cmd.parameters()) {
					yicescmd.append(translate(d.parameter()));
					yicescmd.append("::");
					yicescmd.append(translate(d.sort()));
					yicescmd.append(" ");
				}
				yicescmd.append(") ");
				yicescmd.append(translate(cmd.expression()));
				yicescmd.append(")");
			}
			yicescmd.append(")");
			IResponse response = send(null,yicescmd.toString());
			if (response != null) return response;
			return status;

		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("assert command failed: " + e.getMessage());
		}

	}

	@Override
	public IResponse declare_sort(Ideclare_sort cmd) {
		try {
			IResponse status = super.declare_sort(cmd);
			if (!status.isOK()) return status;
			
			if (cmd.arity().intValue() == 0) {
				IResponse response = send(cmd.sortSymbol().pos(),"(define-type " + translate(cmd.sortSymbol()) + ")");
				if (response != null) return response;
			} else {
				throw new IVisitor.VisitorException("Yices2 does not support defining parameterized types",null);
			}
			return status;
			
			// FIXME - Yices does not seem to allow creating arbitrary new types
			// Besides Yices uses structural equivalence.

		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Yices2 declare-sort command failed: " + e.getMessage(),e.pos());
		}

	}

	@Override
	public IResponse define_sort(Idefine_sort cmd) {
		try {
			IResponse status = super.define_sort(cmd);
			if (!status.isOK()) return status;

			if (cmd.parameters().size() == 0) {
				String msg = "(define-type " + translate(cmd.sortSymbol()) + " ";
				msg = msg + translate(cmd.expression()) + ")";
				IResponse response = send(cmd.sortSymbol().pos(),msg);
				if (response != null) return response;
			} else {
				throw new IVisitor.VisitorException("Yices2 does not support defining parameterized types",null);
			}
			return status;

			// FIXME - Yices does not seem to allow creating arbitrary new types
				// Besides Yices uses structural equivalence.

		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Yices2 define-sort command failed: " + e.getMessage(),e.pos());
		}

	}

	@Override 
	public IResponse get_proof() {
		IResponse status = super.get_proof();
		if (status.isError()) return status;
		try {
			String response = solverProcess.sendAndListen("(get-proof)\n");
			if (response.contains(errorIndication)) {
				return smtConfig.responseFactory.error(response);
			}
			return smtConfig.responseFactory.unsupported(); // FIXME - need to return the proof
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Yices2 solver: " + e);
		}
	}

	@Override 
	public IResponse get_unsat_core() {
		IResponse status = super.get_unsat_core();
		if (status.isError()) return status;
		try {
			String response = solverProcess.sendAndListen("(get-unsat-core)\n");
			if (response.contains(errorIndication)) {
				return smtConfig.responseFactory.error(response);
			}
			return smtConfig.responseFactory.unsupported(); // FIXME - need to return the unsat core
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Yices2 solver: " + e);
		}
	}

	@Override 
	public IResponse get_assignment() {
		IResponse status = super.get_assignment();
		if (status.isError()) return status;
		try {
			String response = solverProcess.sendAndListen("(get-assignment)\n");
			if (response.contains(errorIndication)) {
				return smtConfig.responseFactory.error(response);
			}
			return smtConfig.responseFactory.unsupported(); // FIXME - need to return the assignment
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Yices2 solver: " + e);
		}
	}

	@Override 
	public IResponse get_value(IExpr... terms) {
		IResponse status = super.get_value(terms);
		if (status.isError()) return status;
		try {
			// FIMXE - only one term at a time
			IResponse.IFactory factory = smtConfig.responseFactory;
			String response = null;
			List<IPair<IExpr,IExpr>> list = new LinkedList<IPair<IExpr,IExpr>>();
			for (IExpr e: terms) {
				String s = "(eval " + translate(e) + ")\n";
				response = solverProcess.sendAndListen(s);
				if (response.contains(errorIndication)) {
					return smtConfig.responseFactory.error(response);
				}
				IExpr r = parseYicesResponse(response);
				if (r == null) return factory.error("Don't know how to parse " + response);

				IPair<IExpr,IExpr>  p = factory.pair(e,r);
				list.add(p);
			}
			return factory.get_value_response(list);
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Error writing to Yices2 solver: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Error translating for Yices2: " + e.getMessage());
		}
	}
	
	protected IExpr parseYicesResponse(String response) {
//		try {
			response = response.trim();
			IResponse.IFactory factory = smtConfig.responseFactory;
			IExpr.IFactory f = smtConfig.exprFactory;
			if ("true".equals(response) || "false".equals(response)) {
				return f.symbol(response);
			}
			try {
				Integer i = Integer.valueOf(response);
				return f.numeral(i);
			} catch (Exception e) {
				// continue
			}
			if (response.contains("stdin")) return null;
			if (response.charAt(0) != '(' && !response.contains(" ")) return f.symbol(response);
			
//			Pattern oldbv = Pattern.compile("bv([0-9]+)\\[([0-9]+)\\]");
//			Matcher mm = oldbv.matcher(response);
//			while (mm.find()) {
//				long val = Long.parseLong(mm.group(1));
//				int base = Integer.parseInt(mm.group(2));
//				String bits = "";
//				for (int i=0; i<base; i++) { bits = ((val&1)==0 ? "0" : "1") + bits; val = val >>> 1; }
//				response = response.substring(0,mm.start()) + "#b" + bits + response.substring(mm.end(),response.length());
//				mm = oldbv.matcher(response);
//			}
//			if (response.contains("error")) {
//				// is this right for Yices2?
//				// FIXME - (1) the {Print} also needs {Space}; (2) err_getValueTypes.tst returns a non-error s-expr and then an error s-expr - this fails for that case
//				//Pattern p = Pattern.compile("\\p{Space}*\\(\\p{Blank}*error\\p{Blank}+\"(([\\p{Space}\\p{Print}^[\\\"\\\\]]|\\\\\")*)\"\\p{Blank}*\\)\\p{Space}*");
//				Pattern p = Pattern.compile("\\p{Space}*\\(\\p{Blank}*error\\p{Blank}+\"(([\\p{Print}\\p{Space}&&[^\"\\\\]]|\\\\\")*)\"\\p{Blank}*\\)");
//				Matcher m = p.matcher(response);
//				String concat = "";
//				while (m.lookingAt()) {
//					if (!concat.isEmpty()) concat = concat + "; ";
//					String matched = m.group(1);
//					concat = concat + matched;
//					m.region(m.end(0),m.regionEnd());
//				}
//				if (!concat.isEmpty()) response = concat;
//				return smtConfig.responseFactory.error(response);
//			}
//			org.smtlib.sexpr.Parser responseParser = new org.smtlib.sexpr.Parser(smt(),new Pos.Source(response,null));
//			return responseParser.parseResponse(response);
			return null;
//		} catch (ParserException e) {
//			return smtConfig.responseFactory.error("ParserException while parsing response: " + response + " " + e);
//		}
	}


	
	public /*@Nullable*/ String translate(IExpr expr) throws IVisitor.VisitorException {
		return expr.accept(new Translator());
	}
	
	public /*@Nullable*/ String translate(ISort expr) throws IVisitor.VisitorException {
		return expr.accept(new Translator());
	}
	
	/* Yices does not distinguish formulas and terms, so the mapping
	 * from SMT-LIB is simpler.
	 */
	
	static Map<String,String> fcnNames = new HashMap<String,String>();
	static Set<String> logicNames = new HashSet<String>();
	static {
		/* SMTLIB			YICES
		 * (or p q r ...)	(or p q r ...)
		 * (and p q r ...)	(and p q r ...)
		 * (not p)			(not p)
		 * (=> p q r ...)	(=> p (=> q r...))
		 * (xor p q r ...)	(/= (/= p q)) r )) ...
		 * (= p q r ...)	(and (= p q) (= q r) ... ) 
		 * (distinct p q r)	 conjunction of /= 
		 * true				true
		 * false			false
		 * (ite b p q)		(if b p q)
		 * (forall ...		(forall (a::Bool b::Int) expr)
		 * (exists ...		(exists (a::Bool b::Int) expr)
		 * (let ...			(let ((aux::int (f (f x)))) (g aux aux))
		 * 
		 * < <= > >=		< <= > >=  : no chaining allowed
		 *
		 * TERMS
		 * + - *			+ - * : left associative
		 * 	    			select store  - for arrays
		 * 
		 * 
		 * Yices has / mod div
		 */
		
	}
	

	/* Yices ids:
	 * 		FIXME - not  defined what Yices ids can be made of
	 */
	
	static Map<String,String> bvfcns = new HashMap<String,String>();
	static {
		bvfcns.put("bvadd","bv-add");
		bvfcns.put("bvand","bv-and");
		bvfcns.put("bvor","bv-or");
		bvfcns.put("bvmul","bv-mul");
		bvfcns.put("bvshl","bv-shift-left0"); // second argument is an integer
		bvfcns.put("bvlshr","bv-shift-right0"); // second argument is an integer
		bvfcns.put("bvneg","bv-neg");
		bvfcns.put("bvnot","bv-not");
		bvfcns.put("bvudiv","");
		bvfcns.put("bvurem","");
		bvfcns.put("concat","bv-concat");
		bvfcns.put("extract","bv-extract");
		bvfcns.put("bvult","bv-lt");
		bvfcns.put("bvnand","");
		bvfcns.put("bvnor","");
		bvfcns.put("bvxor","");
		bvfcns.put("bvxnor","");
		bvfcns.put("bvcomp","");
		bvfcns.put("bvsub","");
		bvfcns.put("bvsdiv","");
		bvfcns.put("bvsrem","");
		bvfcns.put("bvsmod","");
		bvfcns.put("bvashr","");
		bvfcns.put("bvule","");
		bvfcns.put("bvugt","");
		bvfcns.put("bvuge","");
		bvfcns.put("bvslt","");
		bvfcns.put("bvsle","");
		bvfcns.put("bvsgt","");
		bvfcns.put("bvsge","");
	}

	
	public class Translator extends IVisitor.NullVisitor<String> {
		
		public Translator() {}
		
		protected String encode(IAttributeValue sym) {
			return org.smtlib.sexpr.Printer.write(sym); // FIXME - is this OK?
		}

		@Override
		public String visit(IDecimal e) throws IVisitor.VisitorException {
			throw new VisitorException("The yices2 solver cannot handle decimal literals",e.pos());
		}

		@Override
		public String visit(IStringLiteral e) throws IVisitor.VisitorException {
			throw new VisitorException("The yices2 solver cannot handle string literals",e.pos());
		}

		@Override
		public String visit(INumeral e) throws IVisitor.VisitorException {
			return e.value().toString();
		}

		@Override
		public String visit(IBinaryLiteral e) throws IVisitor.VisitorException {
			return "0b" + e.value();
		}

		@Override
		public String visit(IHexLiteral e) throws IVisitor.VisitorException {
			// Convert to binary literal
			final String[] bits = { "0000", "1000", "0100", "1100", "0010", "1010", "0110", "1110", "0001", "1001", "0101", "1101", "0011", "1011", "0111", "1111" };
			StringBuilder s = new StringBuilder();
			for (int i = 0; i < e.value().length(); i++) {
				char c = e.value().charAt(i);
				int k = c <= '9' ? (c-'0') : c <= 'Z' ? (c - 'A' + 10) : (c - 'a' + 10);
				s.append(bits[k]);
			}
			return s.toString();
		}
		

		@Override
		public String visit(IFcnExpr e) throws IVisitor.VisitorException {
			Iterator<IExpr> iter = e.args().iterator();
			if (!iter.hasNext()) throw new VisitorException("Did not expect an empty argument list",e.pos());
			IQualifiedIdentifier fcn = e.head();
			String fcnname = fcn.headSymbol().accept(this);
			// FIXME - should we be doing these comparisons with strings?
			if (fcn instanceof ParameterizedIdentifier && fcn.headSymbol().toString().equals(fcnname)) {
				throw new VisitorException("Unknown parameterized function symbol: " + fcnname, e.pos());
			}
			StringBuilder sb = new StringBuilder();
			int length  = e.args().size();
			if (fcnname.equals("or") || fcnname.equals("and")) {
				// operators that are still multi-arity
				sb.append("( ");
				sb.append(fcnname);
				while (iter.hasNext()) {
					sb.append(" ");
					sb.append(iter.next().accept(this));
				}
				sb.append(" )");
				return sb.toString();
			} else if (fcnname.equals("=") || fcnname.equals("<") || fcnname.equals(">") || fcnname.equals("<=") || fcnname.equals(">=")) {
				// chainable
				return remove_chainable(fcnname,iter);
			} else if (fcnname.equals("xor")) {
				fcnname = "/=";
				// left-associative operators that need grouping
				return remove_leftassoc(fcnname,length,iter);
			} else if (fcnname.equals("=>")) {
				// right-associative operators that need grouping
				if (!iter.hasNext()) {
					throw new VisitorException("=> operation without arguments",e.pos());
				}
				return remove_rightassoc(fcnname,iter);
			} else if (fcnname.equals("distinct")) {
				if (length == 2) {
					sb.append("(/=");
					while (iter.hasNext()) {
						sb.append(" ");
						sb.append(iter.next().accept(this));
					}
					sb.append(")");
				} else {
					int j = 0;
					sb.append("(and");
					while (iter.hasNext()) {
						IExpr n = iter.next();
						for (int k = 0; k<j; k++) {
							sb.append(" (/= ");
							sb.append(n.accept(this));
							sb.append(" ");
							sb.append(e.args().get(k).accept(this));
							sb.append(")");
						}
						++j;
					}
					sb.append(")");
				}
				return sb.toString();
			} else if (length == 1 && fcnname.equals("-")) {
				// In yices there is no negation: (- x) is just x
				// We express negation with (- 0 x)
				sb.append("(- 0 ");
				sb.append(iter.next().accept(this));
				sb.append(" )");
				return sb.toString();
			} else if (length == 2 && symTable.arrayTheorySet && fcnname.equals("select")) {
				sb.append("(");
				sb.append(iter.next().accept(this));
				sb.append(" ");
				sb.append(iter.next().accept(this));
				sb.append(")");
				return sb.toString();
			} else if (length == 3 && symTable.arrayTheorySet && fcnname.equals("store")) {
				sb.append("(update ");
				sb.append(iter.next().accept(this));
				sb.append(" (");
				sb.append(iter.next().accept(this));
				sb.append(") ");
				sb.append(iter.next().accept(this));
				sb.append(")");
				return sb.toString();
			} else {
				if (symTable.bitVectorTheorySet) {
					// Predefined: bvadd, bvmul, bvneg, bvnot, bvshl, bvlshr, concat, extract, bvult, bvudiv, bvurem, bvand, bvor
					String newname = bvfcns.get(fcnname);
					if (newname == null) {
						// continue
					} else if (newname.isEmpty()) {
						throw new VisitorException("The BitVector function " + fcnname + " is not implemented in yices",e.pos());
					} else if (fcnname.equals("extract")) {
						sb.append("(bv-extract ");
						IParameterizedIdentifier pid = (IParameterizedIdentifier)fcn;
						sb.append(pid.numerals().get(1).intValue());
						sb.append(" ");
						sb.append(pid.numerals().get(0).intValue());
						sb.append(" ");
						sb.append(iter.next().accept(this));
						sb.append(")");
						return sb.toString();
					} else if (fcnname.equals("bvshl") || fcnname.equals("bvlshr")) {
						throw new VisitorException("The BitVector function " + fcnname + " is not implementetd in yices",e.pos());
					} else {
						fcnname = newname;
					}
				}
				// no associativity 
				sb.append("( ");
				sb.append(fcnname);
				while (iter.hasNext()) {
					sb.append(" ");
					sb.append(iter.next().accept(this));
				}
				sb.append(" )");
				return sb.toString();
			}
		}
			
		//@ requires iter.hasNext();
		private <T extends IExpr> String remove_rightassoc(String fcnname, Iterator<T> iter ) throws IVisitor.VisitorException {
			T n = iter.next();
			if (!iter.hasNext()) {
				return n.accept(this);
			} else {
				StringBuilder sb = new StringBuilder();
				sb.append("(");
				sb.append(fcnname);
				sb.append(" ");
				sb.append(n.accept(this));
				sb.append(" ");
				sb.append(remove_rightassoc(fcnname,iter));
				sb.append(")");
				return sb.toString();
			}
		}

		//@ requires iter.hasNext();
		//@ requires length > 0;
		private <T extends IExpr> String remove_leftassoc(String fcnname, int length, Iterator<T> iter ) throws IVisitor.VisitorException {
			if (length == 1) {
				return iter.next().accept(this);
			} else {
				StringBuilder sb = new StringBuilder();
				sb.append("(");
				sb.append(fcnname);
				sb.append(" ");
				sb.append(remove_leftassoc(fcnname,length-1,iter));
				sb.append(" ");
				sb.append(iter.next().accept(this));
				sb.append(")");
				return sb.toString();
			}
		}
		
		//@ requires iter.hasNext();
		//@ requires length > 0;
		private <T extends IAccept> String remove_chainable(String fcnname, Iterator<T> iter ) throws IVisitor.VisitorException {
			StringBuilder sb = new StringBuilder();
			sb.append("(and ");
			T left = iter.next();
			while (iter.hasNext()) {
				sb.append("(");
				sb.append(fcnname);
				sb.append(" ");
				sb.append(left.accept(this));
				sb.append(" ");
				sb.append((left=iter.next()).accept(this));
				sb.append(")");
			}
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(ISymbol e) throws IVisitor.VisitorException {
			return e.value(); // FIXME - translate
		}

		@Override
		public String visit(IKeyword e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Keyword in an expression to be translated",e.pos());
		}

		@Override
		public String visit(IError e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Error token in an expression to be translated", e.pos());
		}

		@Override
		public String visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
			// FIXME - use default printer properly to print Symbol
			throw new IVisitor.VisitorException("Unsupported parameterized function symbol: " + e.headSymbol().toString(),e.pos());
		}

		@Override
		public String visit(IAsIdentifier e) throws IVisitor.VisitorException {
			throw new UnsupportedOperationException("visit-IAsIdentifier");
		}

		@Override
		public String visit(IForall e) throws IVisitor.VisitorException {
			StringBuffer sb = new StringBuffer();
			boolean allBool = true;
			long bits = 1; // FIXME - no more than 63 quantifiers
			for (IDeclaration p: e.parameters()) {
				if (!p.sort().isBool()) allBool = false;
				bits = bits << 1;
			}
			if (allBool) {
				sb.append("(and ");
				while (--bits >= 0) {
					sb.append("(let (");
					long k = bits;
					for (IDeclaration p: e.parameters()) {
						sb.append("(");
						sb.append(p.parameter().accept(this));
						sb.append(" ");
						sb.append((k&1) == 1 ? "true" : "false");
						sb.append(")");
						k = k >>> 1;
					}
				    sb.append(") ");
				    sb.append(e.expr().accept(this));
				    sb.append(") ");
				}
				sb.append(")");
			} else {
				sb.append("(forall (");
				for (IDeclaration d: e.parameters()) {
					sb.append(d.parameter().accept(this));
					sb.append("::");
					sb.append(d.sort().accept(this));
					sb.append(" ");
				}
				sb.append(") ");
				sb.append(e.expr().accept(this));
				sb.append(")");
			}
			return sb.toString();
		}

		@Override
		public String visit(IExists e) throws IVisitor.VisitorException {
			StringBuffer sb = new StringBuffer();
			boolean allBool = true;
			long bits = 1; // FIXME - no more than 63 quantifiers
			for (IDeclaration p: e.parameters()) {
				if (!p.sort().isBool()) allBool = false;
				bits = bits << 1;
			}
			if (allBool) {
				sb.append("(or ");
				while (--bits >= 0) {
					sb.append("(let (");
					long k = bits;
					for (IDeclaration p: e.parameters()) {
						sb.append("(");
						sb.append(p.parameter().accept(this));
						sb.append(" ");
						sb.append((k&1) == 1 ? "true" : "false");
						sb.append(")");
						k = k >>> 1;
					}
				    sb.append(") ");
				    sb.append(e.expr().accept(this));
				    sb.append(") ");
				}
				sb.append(")");
			} else {
				sb.append("(exists (");
				for (IDeclaration d: e.parameters()) {
					sb.append(d.parameter().accept(this));
					sb.append("::");
					sb.append(d.sort().accept(this));
					sb.append(" ");
				}
				sb.append(") ");
				sb.append(e.expr().accept(this));
				sb.append(")");
			}
			return sb.toString();
		}

		@Override
		public String visit(ILet e) throws IVisitor.VisitorException {
			StringBuffer sb = new StringBuffer();
			sb.append("(let (");
			for (IBinding d: e.bindings()) {
				sb.append("(");
				sb.append(d.parameter().accept(this));
				sb.append(" ");
				sb.append(d.expr().accept(this));
				sb.append(")");
			}
			sb.append(") ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(IAttribute<?> e) throws IVisitor.VisitorException {
			throw new UnsupportedOperationException("visit-IAttribute");
		}

		@Override
		public String visit(IAttributedExpr e) throws IVisitor.VisitorException {
			IExpr expr = e.expr();
			IAttribute<?> attr = e.attributes().get(0);
			if (attr.keyword().toString().equals(":named")) {
				String name = encode(attr.attrValue());
				String ex = expr.accept(this);
				String sort = typemap.get(expr).accept(this);
				String def = "(define " + name + "::" + sort + " " + ex + ")";
				IResponse response = send(e.pos(),def);
				if (response != null) {
					throw new VisitorException("Failed to define attributed expression: " + response, e.pos()); // FIXME - error message format?
				}
				return ex;
			} else {
				throw new VisitorException("Unexpected kind of keyword: " + smtConfig.defaultPrinter.toString(attr.keyword()),attr.pos());
			}
		}

		@Override
		public String visit(IDeclaration e) throws IVisitor.VisitorException {
			throw new UnsupportedOperationException("visit-IDeclaration");
		}

		@Override
		public String visit(ISort.IFamily s) throws IVisitor.VisitorException {
			return s.identifier().accept(this);
		}
		
		@Override
		public String visit(ISort.IAbbreviation s) throws IVisitor.VisitorException {
			throw new UnsupportedOperationException("visit-ISort.IAbbreviation");
		}
		
		@Override
		public String visit(ISort.IApplication s) throws IVisitor.VisitorException {
			if (s.isBool()) return "bool";
			String sort = s.family().headSymbol().accept(this);
			if (s.parameters().size() == 0) {
				if ("Int".equals(sort)) return "int";
				if ("Real".equals(sort)) return "real";
				if (symTable.bitVectorTheorySet && "BitVec".equals(sort)) {
					String sbv = "(bitvector ";
					int k = ((IParameterizedIdentifier)s.family()).numerals().get(0).intValue();
					sbv = sbv + k + ")";
					return sbv;
				}
				return sort;
			} else {
				if (symTable.arrayTheorySet && "Array".equals(sort)) {
					StringBuilder sb = new StringBuilder();
					sb.append("(-> ");
					sb.append(s.parameters().get(0).accept(this));
					sb.append(" ");
					sb.append(s.parameters().get(1).accept(this));
					sb.append(")");
					return sb.toString();
				}
				throw new VisitorException("Yices does not support user-defined parameterized sorts: " + s, s.pos());
			}
		}
		
		@Override
		public String visit(ISort.IFcnSort s) {
			throw new UnsupportedOperationException("visit-ISort.IFcnSort");
		}
		
		@Override
		public String visit(ISort.IParameter s) {
			throw new UnsupportedOperationException("visit-ISort.IParameter");
		}
		
		
	}
}
