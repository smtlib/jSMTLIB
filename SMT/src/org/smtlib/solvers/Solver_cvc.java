/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.IOException;
import java.math.BigDecimal;
import java.util.*;

import org.smtlib.*;
import org.smtlib.ICommand.*;
import org.smtlib.ICommand.Idefine_fun;
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
import org.smtlib.IExpr.IIdentifier;
import org.smtlib.IExpr.IKeyword;
import org.smtlib.IExpr.ILet;
import org.smtlib.IExpr.INumeral;
import org.smtlib.IExpr.IParameterizedIdentifier;
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort.IExpression;
import org.smtlib.IVisitor.VisitorException;

/** This class implements the adapter of SMTv2 to old CVC commands. */ 
public class Solver_cvc extends Solver_test implements ISolver {
	/** Holds the options for the command-line that invokes the solver;
	 * cmds[0] is filled in with the local file-system path to the executable
	 */
	String cmds[] = new String[]{ "", "+int" }; 
	
	//private IResponse status;

	/** The external process driver, initialized in start() */
	private SolverProcess solverProcess;
	
	final private String errorIndication = "rror";
	
	/** Creates a solver object (which is not yet started)*/
	public Solver_cvc(SMT.Configuration smtConfig, String executable) {
		super(smtConfig,"");
		cmds[0] = executable;
		solverProcess = new SolverProcess(cmds,"CVC> ","solver.out.cvc");
	}
	
	@Override
	public IResponse start() {
		super.start();
		try {
			solverProcess.start();
//			String response = solverProcess.sendAndListen("DATATYPE T$$PBOOL = _$TRUE | _$FALSE END;\n");
//			if (response.contains(errorIndication)) {
//				return smtConfig.responseFactory.error(response);
//			}
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Started cvc " );
			return smtConfig.responseFactory.success();
		} catch (Exception e) {
			return smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}
	
	@Override
	public IResponse exit() {
		super.exit();
		solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("Ended CVC ");
		return smtConfig.responseFactory.success_exit();
	}



	@Override
	public IResponse assertExpr(IExpr sexpr) {
		try {
			IResponse status = super.assertExpr(sexpr);
			if (!status.isOK()) return status;
			String response = solverProcess.sendAndListen("ASSERT " + translate(sexpr) + " ;\n");
			if (response.contains(errorIndication)) {
				return smtConfig.responseFactory.error(response);
			}
			return status;
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to assert expression: " + e + " " + sexpr, sexpr.pos());
		} catch (VisitorException e) {
			return smtConfig.responseFactory.error(e.getMessage(),e.pos());
		}
	}

	@Override
	public IResponse check_sat() {
		IResponse res;
		IResponse status = super.check_sat();
		if (status.isError()) return status;
		try {
			String s = solverProcess.sendAndListen("CHECKSAT;\r\n");
			//System.out.println("HEARD: " + s);
			if (s.contains(errorIndication)) {
				return smtConfig.responseFactory.error(s);
			}
			if (s.contains("Unsatisfiable.")) res = smtConfig.responseFactory.unsat();
			else if (s.contains("Satisfiable.")) res = smtConfig.responseFactory.sat();
			else res = smtConfig.responseFactory.unknown();
			checkSatStatus = res;
		} catch (IOException e) {
			res = smtConfig.responseFactory.error("Failed to check-sat",null);
		}
		return res;
	}

//	@Override
//	public CommandResult defineFun(SExpr sexpr) {
//		// TODO Auto-generated method stub
//		return null;
//	}
//
	@Override
	public IResponse pop(int number) {
		try {
			IResponse status = super.pop(number);
			if (!status.isOK()) return status;
			if (number == 0) return smtConfig.responseFactory.success();
			while (number-- > 0) {
				String response = solverProcess.sendAndListen("POP;\n");
				if (response.contains(errorIndication)) {
					return smtConfig.responseFactory.error(response);
				}
			}
			return status;
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to execute pop: " + e);
		}
	}

	@Override
	public IResponse push(int number) {
		try {
			IResponse status = super.push(number);
			if (!status.isOK()) return status;
			if (number == 0) return smtConfig.responseFactory.success();
			while (number-- > 0) {
				String response = solverProcess.sendAndListen("PUSH;\n");
				if (response.contains(errorIndication)) {
					return smtConfig.responseFactory.error(response);
				}
			}
			return smtConfig.responseFactory.success();
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to execute push: " + e);
		}
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		return super.set_logic(logicName,pos);
	}

	@Override
	public IResponse set_option(IKeyword key, IAttributeValue value) {
		return super.set_option(key,value);
	}

	@Override
	public IResponse get_option(IKeyword key) {
		return super.get_option(key);
	}

	@Override
	public IResponse get_info(IKeyword key) {
		String option = key.value();
		if (":error-behavior".equals(option)) {
			return smtConfig.responseFactory.continued_execution(); // FIXME - is this true?
		} else if (":status".equals(option)) {
			return checkSatStatus==null ? smtConfig.responseFactory.unsupported() : checkSatStatus; 
		} else if (":all-statistics".equals(option)) {
			return smtConfig.responseFactory.unsupported(); // FIXME
		} else if (":reason-unknown".equals(option)) {
			return smtConfig.responseFactory.unsupported(); // FIXME
		} else if (":authors".equals(option)) {
			return smtConfig.responseFactory.stringLiteral("Clark Barrett, Cesare Tinelli, and others");
		} else if (":version".equals(option)) {
			return smtConfig.responseFactory.stringLiteral("2.2"); // FIXME
		} else if (":name".equals(option)) {
			return smtConfig.responseFactory.stringLiteral("CVC3");
		} else {
			return smtConfig.responseFactory.unsupported();
		}
	}
	
	
	@Override
	public IResponse declare_fun(Ideclare_fun cmd){
		try {
			IResponse status = super.declare_fun(cmd);
			if (!status.isOK()) return status;
			String encodedName = translate(cmd.symbol());
			String msg = encodedName + ":";
			if (cmd.argSorts().size() == 0) {
				msg = msg + translate(cmd.resultSort());
			} else if (cmd.argSorts().size() == 1) {
				msg = msg + translate(cmd.argSorts().get(0));
				msg = msg + "->";
				msg = msg + translate(cmd.resultSort());
			} else {
				Iterator<ISort> iter = cmd.argSorts().iterator();
				msg = msg + "(" + translate(iter.next());
				while (iter.hasNext()) {
					msg = msg + "," + translate(iter.next());
				}
				msg = msg + ")->";
				msg = msg + translate(cmd.resultSort());
			}
			msg = msg + ";\n";
			String response = solverProcess.sendAndListen(msg);
			if (response.contains(errorIndication)) {
				return smtConfig.responseFactory.error(response);
			}
			return smtConfig.responseFactory.success();
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to execute set_logic: " + e);
		} catch (IVisitor.VisitorException e) {
			return smtConfig.responseFactory.error("Failed to execute set_logic: " + e, e.pos());
		}
		
	}
	
	public String encodeSort(IIdentifier id) throws VisitorException {
		if (id instanceof ISymbol) {
			String nm = org.smtlib.sexpr.Printer.write(id);
			if ("Bool".equals(nm)) return "BOOLEAN";
			if ("Int".equals(nm)) return "INT";
			if ("Real".equals(nm)) return "REAL";
			if ("Array".equals(nm)) {
				if (!symTable.arrayTheorySet) {
					throw new VisitorException("Array logic not enabled",id.pos());
				}
				return "ARRAY";
			}
			return "T$" + nm;
		} else if (id instanceof IParameterizedIdentifier){
			IParameterizedIdentifier pid = (IParameterizedIdentifier)id;
			ISymbol head = pid.headSymbol();
			String nm = org.smtlib.sexpr.Printer.write(head);
			if ("BitVec".equals(nm)) {
				return "BITVECTOR(" + pid.numerals().get(0) + ")";
			}
			nm = "T$" + nm;
			for (INumeral n: pid.numerals()) {
				nm = nm + "$_" + org.smtlib.sexpr.Printer.write(n);
			}
			return nm;
		} else {
			throw new VisitorException("Unexpected kind of identifier: " + id.getClass(),id.pos());
		}
	}
	
	@Override
	public IResponse declare_sort(Ideclare_sort cmd) {
		IResponse res = super.declare_sort(cmd);
		if (!res.isOK()) return res;
		try {
			if (cmd.arity().value().intValue() == 0) {
				String msg = encodeSort(cmd.sortSymbol()) + ": TYPE;\n";
				String response = solverProcess.sendAndListen(msg);
				if (response.contains(errorIndication)) {
					return smtConfig.responseFactory.error(response);
				}
				return res;
			} else {
				return smtConfig.responseFactory.error("CVC adapter does not implement parameterized user-defined sorts",cmd instanceof IPos.IPosable ? ((IPos.IPosable)cmd).pos() : null);
			}
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to execute declare_sort: " + e);
		} catch (VisitorException e) {
			return smtConfig.responseFactory.error("Failed to execute declare_sort: " + e, e.pos());
		}
	}

	@Override
	public IResponse define_fun(Idefine_fun cmd) {
		IResponse res = super.define_fun(cmd);
		if (!res.isOK()) return res;
		try {
			if (cmd.parameters().size() == 0) {
				String name = encode(cmd.symbol());
				String resultSort = translate(cmd.resultSort());
				String def = cmd.expression() == null ? null : translate(cmd.expression());
				def = name + ": " + resultSort + 
					( def == null ? "" : (" = " + def )) + 
					";\n";
				String response = solverProcess.sendAndListen(def);
				if (response.contains(errorIndication)) {
					return smtConfig.responseFactory.error(response);
				}
				return res;
			} else {
				String name = encode(cmd.symbol());
				StringBuilder def = new StringBuilder();
				def.append(name);
				def.append(" : ");
				if (cmd.parameters().size() == 1) {
					def.append(translate(cmd.parameters().get(0).sort()));
				} else {
					def.append("(");
					Iterator<IDeclaration> iter = cmd.parameters().iterator();
					def.append(translate(iter.next().sort()));
					while (iter.hasNext()) {
						def.append(",");
						def.append(translate(iter.next().sort()));
					}
				}
				def.append(")->");
				def.append(translate(cmd.resultSort()));
				def.append(" = LAMBDA(");
				Iterator<IDeclaration> iter = cmd.parameters().iterator();
				IDeclaration d = iter.next();
				if (cmd.parameters().size() == 1) {
					def.append(translate(d.parameter()));
					def.append(":");
					def.append(translate(d.sort()));
				} else {
					def.append(translate(d.parameter()));
					def.append(":");
					def.append(translate(d.sort()));
					while (iter.hasNext()) {
						def.append(",");
						d = iter.next();
						def.append(translate(d.parameter()));
						def.append(":");
						def.append(translate(d.sort()));
					}
				}
				def.append("): ");
				def.append(translate(cmd.expression()));
				def.append(";\n");
				String response = solverProcess.sendAndListen(def.toString());
				if (response.contains(errorIndication)) {
					return smtConfig.responseFactory.error(response);
				}
				return res;
			}
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to execute define_fun: " + e);
		} catch (VisitorException e) {
			return smtConfig.responseFactory.error("Failed to execute define_fun: " + e, e.pos());
		}
	}

	@Override
	public IResponse define_sort(Idefine_sort cmd) {
		IResponse res = super.define_sort(cmd);
		if (!res.isOK()) return res;
		try {
			if (cmd.parameters().size() == 0) {
				String def = translate(cmd.expression());
				String head = encodeSort(cmd.sortSymbol());
				def = head + ": TYPE = " + def + ";\n";
				String response = solverProcess.sendAndListen(def);
				if (response.contains(errorIndication)) {
					return smtConfig.responseFactory.error(response);
				}
				return res;
			} else {
				return smtConfig.responseFactory.error("Parameterized sort definitions not implemented"); // FIXME
			}
		} catch (IOException e) {
			return smtConfig.responseFactory.error("Failed to execute define_sort: " + e);
		} catch (VisitorException e) {
			return smtConfig.responseFactory.error("Failed to execute define_sort: " + e, e.pos());
		}
	}

	public String translate(IExpr expr) throws IVisitor.VisitorException {
		return expr.accept(new Translator(typemap,smtConfig));
	}
	
	public String translate(ISort expr) throws IVisitor.VisitorException {
		return expr.accept(new Translator(typemap,smtConfig));
	}
	
	/* CVC does distinguish formulas and terms, but allows
	 * BOOLEAN terms
	 */
	
	static Map<String,String> fcnNames = new HashMap<String,String>();
	static Set<String> logicNames = new HashSet<String>();
	static {
		/* SMTLIB			CVC
		 * (or p q r ...)	(p OR q OR r ...)
		 * (and p q r ...)	(p AND q AND r ...)
		 * (not p)			(NOT p)
		 * (=> p q r ...)	(p => (q => r)) 
		 * (xor p q r ...)	((p XOR q) XOR r)
		 * (= p q r ...)	((p <=> q) AND ( q <=> r) ... )   - formulas
		 * (= p q r ...)	((p = q) AND (q == r) ... )   - terms
		 * (distinct p q r)	(NOT (p == q))   - formulas (error if more than 2 arguments) 
		 * (distinct p q r)	(DISTINCT p q r ... )   - terms  
		 * true				TRUE
		 * false			FALSE
		 * (ite b p q)		(IF b THEN p ELSE q ENDIF)
		 * 
		 */
		
		fcnNames.put("or","|");				// infix for cvc (left-assoc)
		fcnNames.put("and","&");				// infix for cvc (left-assoc)
		fcnNames.put("not","~");				// prefix
		fcnNames.put("=>","=>");				// infix for cvc (right-assoc)
		fcnNames.put("xor","XOR");				// infix for cvc (left-assoc)
		fcnNames.put("=","="); // <=> for formula 	// infix for cvc (chainable)
		fcnNames.put("distinct","DISTINCT"); // XOR for formula// >2 arguments OK for cvc (pairwise)
		fcnNames.put("true","TRUE");
		fcnNames.put("false","FALSE");
		fcnNames.put("ite","IF");			// special in cvc  IF ... THEN ... ELSE ... FI
		fcnNames.put("+","+");				// infix for cvc (left-assoc)
		fcnNames.put("-","-");				// infix for cvc (left-assoc)
		fcnNames.put("*","*");				// infix for cvc (left-assoc)
		fcnNames.put(">",">");				// infix for cvc (left-assoc)		
		fcnNames.put(">=",">=");			// infix for cvc (chainable)
		fcnNames.put("<","<");				// infix for cvc (chainable)
		fcnNames.put("<=","<=");			// infix for cvc (chainable)
		
		fcnNames.put("forall","FORALL");
		fcnNames.put("exists","EXISTS");
		fcnNames.put("let","LET");
		
		fcnNames.put("bvadd","BVPLUS"); // needs a first argument of the number of bits
		fcnNames.put("bvmul","BVMULT"); // needs a first argument of the number of bits
		fcnNames.put("bvneg","BVUMINUS");
		fcnNames.put("bvnot","~");
		fcnNames.put("bvand","&"); // infix
		fcnNames.put("bvor","|"); // infix
		fcnNames.put("bvudiv","&"); // FIXME
		fcnNames.put("bvurem","&"); // FIXME
		fcnNames.put("bvshl","<<"); // infix// FIXME
		fcnNames.put("bvlshr",">>"); // infix// FIXME
		fcnNames.put("concat","@"); // infix
		fcnNames.put("bvult","BVLT");
		fcnNames.put("extract","extract");
		
		logicNames.add("or");
		logicNames.add("and");
		logicNames.add("not");
		logicNames.add("=>");
	}
	
	
	public class Translator extends IVisitor.NullVisitor<String> {
		boolean isFormula = true;
		final private Map<IExpr,ISort> typemap;
		final private SMT.Configuration smtConfig;
		
		public Translator(Map<IExpr,ISort> typemap, SMT.Configuration smtConfig) {
			this.typemap = typemap;
			this.smtConfig = smtConfig;
		}
		
		public /*@Nullable*/ IPos pos(Object e) {
			return e instanceof IPos.IPosable ? ((IPos.IPosable)e).pos() : null;
		}
		
		public String encode(IAttributeValue id) throws VisitorException {
			if (id instanceof ISymbol) {
				return org.smtlib.sexpr.Printer.write(id);
			} else if (id instanceof IParameterizedIdentifier){
				IParameterizedIdentifier pid = (IParameterizedIdentifier)id;
				ISymbol head = pid.headSymbol();
				String nm = org.smtlib.sexpr.Printer.write(head);
				for (INumeral n: pid.numerals()) {
					nm = nm + "$_" + org.smtlib.sexpr.Printer.write(n);
				}
				return nm;
			} else {
				throw new VisitorException("Unexpected kind of identifier: " + id.getClass(),id.pos());
			}
		}
		
		public String encodeSort(IIdentifier id) throws VisitorException {
			return Solver_cvc.this.encodeSort(id);
		}
		
		@Override
		public String visit(IAttributedExpr e) throws IVisitor.VisitorException {
			IExpr expr = e.expr();
			IAttribute<?> attr = e.attributes().get(0);
			if (attr.keyword().toString().equals(":named")) {
				String name = encode(attr.attrValue());
				String ex = expr.accept(this);
				String def = name + " : " + "BOOLEAN" + " = " + ex + ";\n";
				try {
					String response = solverProcess.sendAndListen(def);
					if (response.contains(errorIndication)) {
						throw new VisitorException(response,e.pos());
					}
				} catch (IOException exc) {
					throw new VisitorException("Failed to define attributed expression: " + exc, e.pos());
				}
				return ex;
			} else {
				throw new VisitorException("Unexpected kind of keyword: " + smtConfig.defaultPrinter.toString(attr.keyword()),attr.pos());
			}
		}

		@Override
		public String visit(IDecimal e) throws IVisitor.VisitorException {
			// CVC has rationals for decimal numbers
			BigDecimal v = e.value();
			int scale = v.scale();
			if (scale >= 0) {
				BigDecimal num = v.scaleByPowerOfTen(scale);
				BigDecimal den = BigDecimal.ONE.scaleByPowerOfTen(scale);
				return "(" + num.toBigInteger() + "/" + den.toBigInteger() + ")";
			} else {
				BigDecimal num = v.scaleByPowerOfTen(-scale);
				return "(" + num.toBigInteger() + ")";
			}
		}

		@Override
		public String visit(IStringLiteral e) throws IVisitor.VisitorException {
			throw new VisitorException("The CVC solver cannot handle string literals", pos(e));
		}

		@Override
		public String visit(INumeral e) throws IVisitor.VisitorException {
			return org.smtlib.sexpr.Printer.write(e);
		}

		@Override
		public String visit(IBinaryLiteral e) throws IVisitor.VisitorException {
			// CVC prefix is 0bin - LSB is on right, MSB on left
			return "0bin" + e.value();
		}

		@Override
		public String visit(IHexLiteral e) throws IVisitor.VisitorException {
			// CVC prefix is 0hex - LSB is on right, MSB on left
			return "0hex" + e.value();
		}
		
		//@ requires iter.hasNext();
		private <T extends IExpr> String rightassoc(String fcnname, Iterator<T> iter ) throws IVisitor.VisitorException {
			T n = iter.next();
			if (!iter.hasNext()) {
				return n.accept(this);
			} else {
				StringBuilder sb = new StringBuilder();
				sb.append("(");
				sb.append(n.accept(this));
				sb.append(" ");
				sb.append(fcnname);
				sb.append(" ");
				sb.append(rightassoc(fcnname,iter));
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
				sb.append(remove_leftassoc(fcnname,length-1,iter));
				sb.append(" ");
				sb.append(fcnname);
				sb.append(" ");
				sb.append(iter.next().accept(this));
				sb.append(")");
				return sb.toString();
			}
		}
		
		//@ requires iter.hasNext();
		//@ requires length > 0;
		private <T extends IAccept> String remove_chainable(String newName, int length, Iterator<IExpr> iter ) throws IVisitor.VisitorException {
			StringBuilder sb = new StringBuilder();
			if (length == 2) {
				sb.append("(");
				sb.append(iter.next().accept(this));
				sb.append(" ");
				sb.append(newName);
				sb.append(" ");
				sb.append(iter.next().accept(this));
				sb.append(")");
			} else {
				boolean first = true;
				IExpr left = iter.next();
				sb.append("(");
				while (iter.hasNext()) {
					if (first) first = false; else sb.append(" AND ");
					sb.append("(");
					sb.append(left.accept(this));
					sb.append(" ");
					sb.append(newName);
					sb.append(" ");
					sb.append((left = iter.next()).accept(this));
					sb.append(")");
				}
				sb.append(")");
			}
			return sb.toString();
		}

		Set<String> infix = new HashSet<String>();
		{
			infix.addAll(Arrays.asList(new String[]{"OR","AND","+","*","XOR"}));
		}

		@Override
		public String visit(IFcnExpr e) throws IVisitor.VisitorException {
			boolean resultIsFormula = this.isFormula;
			Iterator<IExpr> iter = e.args().iterator();
			if (!iter.hasNext()) throw new VisitorException("Did not expect an empty argument list", (IPos)e);
			String oldName = e.head().headSymbol().toString();
			String newName = e.head().headSymbol().accept(this);
			int length = e.args().size();
			StringBuilder sb = new StringBuilder();
			try {
				// Determine if the arguments are formulas or terms
				if (resultIsFormula) {
					if (newName != null && logicNames.contains(oldName)) {
						// Propositional boolean item
						this.isFormula = true;
						if (oldName.equals("or")) newName = "OR";
						if (oldName.equals("and")) newName = "AND";
						if (oldName.equals("not")) newName = "NOT";
						if (oldName.equals("=>")) newName = "=>";
					} else {
						IExpr arg = e.args().get(e.args().size() <= 1 ? 0 : 1); // Use argument 1 for ite's sake
						ISort sort = typemap.get(arg);
						if (sort == null) {
							throw new VisitorException("INTERNAL ERROR: Encountered an un-sorted expression node: " + smtConfig.defaultPrinter.toString(arg),arg.pos());
						}
						if (sort.isBool()) {
							// Some functions can take both bool and non-bool arguments:
							//   = /= DISTINCT ite
							this.isFormula = resultIsFormula;
							if ("=".equals(newName)) newName = "<=>";
							else if ("DISTINCT".equals(newName)) {
								if (e.args().size() > 2) {
									return "FALSE";
								} else {
									String a1 = iter.next().accept(this);
									String a2 = iter.next().accept(this);
									return "((" + a1 + ")XOR(" + a2 + "))"; 
								}
							} // FIXME - what about ite?
						} else {
							// Arguments must be terms
							this.isFormula = false;
						}
					}
				} else {
					this.isFormula = false;
				} // FIXME - implies, equality, non-equality, 

				if (infix.contains(newName) || (length >= 2 && newName.equals("-"))) {
					// infix
					sb.append("(");
					sb.append(iter.next().accept(this));
					while (iter.hasNext()) {
						sb.append(" ");
						sb.append(newName);
						sb.append(" ");
						sb.append(iter.next().accept(this));
					}
					sb.append(")");
				} else if (newName.equals("=>")) {
					sb.append(rightassoc(newName,iter));
				} else if (newName.equals("BVXOR")) {
					sb.append(newName);
					sb.append(iter.next().accept(this));
					while (iter.hasNext()) {
						sb.append(",");
						sb.append(iter.next().accept(this));
					}
					sb.append(")");
				} else if (oldName.equals("=")) {
					boolean argsAreBool = typemap.get(e.args().get(0)).isBool();
					boolean needsAnd = length > 2;
					if (needsAnd) sb.append("(");
					String right = iter.next().accept(this);
					while (iter.hasNext()) {
						String left = right;
						right = iter.next().accept(this);
						if (resultIsFormula) {
							sb.append("((");
							sb.append(left);
							sb.append(")");
							sb.append(newName);
							sb.append("(");
							sb.append(right);
							sb.append("))");
						} else {
							throw new VisitorException("CVC does not permit = in terms",e.pos());
						}
						if (needsAnd) {
							if (!iter.hasNext()) sb.append(")");
							else sb.append(" AND ");
						}
					}
				} else if (newName.equals("~") || newName.equals("NOT")) {
					sb.append("(");
					sb.append(newName);
					sb.append(" ");
					sb.append(iter.next().accept(this));
					sb.append(" )");
				} else if (newName.equals("DISTINCT")) {
					if (isFormula) {
						if (length == 2) {
							sb.append("( ");
							sb.append(iter.next().accept(this));
							sb.append(" XOR ");
							sb.append(iter.next().accept(this));
							sb.append(" )");
						} else {
							sb.append("( ");
							boolean first = true;
							while (iter.hasNext()) {
								IExpr left = iter.next();
								Iterator<IExpr> iter2 = e.args().iterator();
								IExpr right;
								while ((right = iter2.next()) != left) {
									if (first) first = false; else sb.append(" AND ");
									sb.append("( ");
									sb.append(left.accept(this));
									sb.append(" XOR ");
									sb.append(right.accept(this));
									sb.append(" )");
								}
							}
							sb.append(" )");
						}
					} else {
						sb.append("DISTINCT(");
						sb.append(iter.next().accept(this));
						while (iter.hasNext()) {
							sb.append(",");
							sb.append(iter.next().accept(this));
						}
						sb.append(")");
					}
				} else if (symTable.arrayTheorySet && oldName.equals("select")) {
					sb.append(iter.next().accept(this));
					sb.append("[");
					sb.append(iter.next().accept(this));
					sb.append("]");
				} else if (symTable.arrayTheorySet && oldName.equals("store")) {
					sb.append("(");
					sb.append(iter.next().accept(this));
					sb.append(" WITH [");
					sb.append(iter.next().accept(this));
					sb.append("] := ");
					sb.append(iter.next().accept(this));
					sb.append(")");
				} else if (oldName.equals("ite")) {
					if (!resultIsFormula) {
						throw new VisitorException("CVC only allows ite constructs at the formula level",e.pos());
					}
					// FIXME - formula only
					sb.append("(IF ");
					sb.append(iter.next().accept(this));
					sb.append(" THEN ");
					sb.append(iter.next().accept(this));
					sb.append(" ELSE ");
					sb.append(iter.next().accept(this));
					sb.append(" ENDIF)");
				} else if (oldName.equals(">") || oldName.equals("<") || oldName.equals(">=") || oldName.equals("<=")) {
					sb.append(remove_chainable(newName,length,iter));
				} else if (length == 1 && newName.equals("-")) {
					sb.append("(");
					sb.append(oldName);
					sb.append(" ");
					sb.append(iter.next().accept(this));
					sb.append(")");
				} else if (symTable.bitVectorTheorySet && oldName.equals("extract")) {
					IParameterizedIdentifier pid = (IParameterizedIdentifier)e.head();
					sb.append(iter.next().accept(this));
					sb.append("[");
					sb.append(org.smtlib.sexpr.Printer.write(pid.numerals().get(1)));
					sb.append(":");
					sb.append(org.smtlib.sexpr.Printer.write(pid.numerals().get(0)));
					sb.append("]");
				} else if (symTable.bitVectorTheorySet && (oldName.equals("bvudiv") || oldName.equals("bvurem") || oldName.equals("bvshl") || oldName.equals("bvlshr"))) {
					throw new VisitorException("SMT BitVector function " + oldName + " is not implemented in cvc",e.pos());
				} else if (symTable.bitVectorTheorySet && ("@".equals(newName) || (oldName.startsWith("bv") && newName != null && newName.charAt(0) != 'B'))) {
					// infix
					sb.append("((");
					sb.append(iter.next().accept(this));
					sb.append(")");
					sb.append(newName);
					sb.append("(");
					sb.append(iter.next().accept(this));
					sb.append("))");
				} else if (symTable.bitVectorTheorySet && (newName.equals("BVPLUS") || newName.equals("BVMULT"))) {
					ISort sort = typemap.get(e);
					int k = 1;
					if (sort instanceof IExpression) {
						IIdentifier id = ((IExpression)sort).family();
						if (id instanceof IParameterizedIdentifier) {
							k = ((IParameterizedIdentifier)id).numerals().get(0).intValue();
						}
					}
					sb.append(newName);
					sb.append("(");
					sb.append(k);
					sb.append(",");
					sb.append(iter.next().accept(this));
					sb.append(",");
					sb.append(iter.next().accept(this));
					sb.append(")");
				} else {
					// usual functional notation
					sb.append(newName == null ? oldName : newName);
					if (!iter.hasNext()) {
						sb.append("()"); // FIXME - should this have no parens at all?
					} else {
						sb.append("(");
						sb.append(iter.next().accept(this));
						while (iter.hasNext()) {
							sb.append(",");
							sb.append(iter.next().accept(this));
						}
						sb.append(")");
					}
				}
			} finally {
				isFormula = resultIsFormula;
			}
			return sb.toString();
		}

		@Override
		public String visit(ISymbol e) throws IVisitor.VisitorException {
			// FIXME - need to check what characters are allowed in a CVC name
			String oldName = e.value();
			if (!isFormula) {
				if ("true".equals(oldName)) return "$_TRUE";
				if ("false".equals(oldName)) return "$_FALSE";
			}
			String newName = fcnNames.get(oldName);
			if (newName != null) {
				// There is a direct translation of a pre-defined SMT-LIB name
				// into a simplify equivalent - use it.
			} else {
				// Use the ? character as an escape
				newName = oldName;
			}
			return newName;
		}

		@Override
		public String visit(IKeyword e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Keyword in an expression to be translated",pos(e));
		}

		@Override
		public String visit(IError e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Error token in an expression to be translated",pos(e));
}

		@Override
		public String visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a IParameterizedIdentifier token in an expression to be translated",pos(e));
		}

		@Override
		public String visit(IForall e) throws IVisitor.VisitorException {
			// FIXME - I think CVC only allows this in formulas
			StringBuilder sb = new StringBuilder();
			sb.append("(FORALL (");
			boolean first = true;
			for (IDeclaration d: e.parameters()) {
				if (first) first = false; else sb.append(", ");
				sb.append(d.parameter().accept(this));
				sb.append(":");
				sb.append(d.sort().accept(this));
			}
			sb.append("): ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(IExists e) throws IVisitor.VisitorException {
			// FIXME - I think CVC only allows this in formulas
			StringBuilder sb = new StringBuilder();
			sb.append("(EXISTS (");
			boolean first = true;
			for (IDeclaration d: e.parameters()) {
				if (first) first = false; else sb.append(", ");
				sb.append(d.parameter().accept(this));
				sb.append(":");
				sb.append(d.sort().accept(this));
			}
			sb.append("): ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		@Override
		public String visit(ILet e) throws IVisitor.VisitorException {
			// FIXME - only in formulas?
			StringBuilder sb = new StringBuilder();
			sb.append("(LET ");
			boolean first = true;
			for (IBinding d: e.bindings()) {
				if (first) first = false; else sb.append(", ");
				sb.append(d.parameter().accept(this));
				sb.append(" = ");
				sb.append(d.expr().accept(this));
			}
			sb.append(" IN ");
			sb.append(e.expr().accept(this));
			sb.append(")");
			return sb.toString();
		}

		public String visit(ISort.IFamily s) throws IVisitor.VisitorException {
			return s.identifier().accept(this);
		}
		
		public String visit(ISort.IAbbreviation s) throws IVisitor.VisitorException {
			throw new UnsupportedOperationException("CVC visit-ISort.IAbbreviation");
		}
		
		public String visit(ISort.IExpression s) throws IVisitor.VisitorException {
			if (s.isBool()) return "BOOLEAN";
			if (s.parameters().size() == 0) {
				String sort = encodeSort(s.family());
				if ("Int".equals(sort)) return "INT";
				if ("Real".equals(sort)) return "REAL";
				return sort; // FIXME - Array, BitVector
			} else if (s.parameters().size() == 2) {
				String sort = encodeSort(s.family());
				if ("ARRAY".equals(sort)) {
					List<ISort> args = s.parameters();
					return "(ARRAY " + args.get(0).accept(this) + " OF " + args.get(1).accept(this) +")";
				} else {
					return "UNKNOWN";
				}
				
			} else {
				return "UNKNOWN"; // FIXME
				//throw new UnsupportedOperationException("CVC visit-ISort.IExpression");
			}
		}
		
		public String visit(ISort.IFcnSort s) {
			throw new UnsupportedOperationException("CVC visit-ISort.IFcnSort");
		}
		public String visit(ISort.IParameter s) {
			throw new UnsupportedOperationException("CVC visit-ISort.IParameter");
		}
	}
}
