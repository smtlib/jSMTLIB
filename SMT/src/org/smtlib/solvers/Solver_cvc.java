/*
 * This file is part of the SMT project.
 * Copyright 2010 David R. Cok
 * Created August 2010
 */
package org.smtlib.solvers;

import java.io.IOException;
import java.lang.reflect.Array;
import java.util.*;

import org.smtlib.ICommand.Ideclare_fun;
import org.smtlib.*;
import org.smtlib.IExpr.IAttributeValue;
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
import org.smtlib.IExpr.IStringLiteral;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IVisitor.VisitorException;

// FIXME - document

public class Solver_cvc extends Solver_test implements ISolver {
	// FIXME - use  -lang smtlib   or -lang smt2  ???
	String cmds[] = new String[]{ "", "+int" }; 
	private IResponse status;
	private SolverProcess solverProcess;
	
	final private String errorIndication = "rror";
	
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
			if (smtConfig.verbose != 0) smtConfig.log.logDiag("Started cvc " );
			return status=smtConfig.responseFactory.success();
		} catch (Exception e) {
			return status=smtConfig.responseFactory.error("Failed to start process " + cmds[0] + " : " + e.getMessage());
		}
	}
	
	@Override
	public IResponse exit() {
		super.exit();
		solverProcess.exit();
		if (smtConfig.verbose != 0) smtConfig.log.logDiag("Ended CVC ");
		return status = smtConfig.responseFactory.success_exit();
	}



	@Override
	public IResponse assertExpr(IExpr sexpr) {
		try {
			status = super.assertExpr(sexpr);
			if (!status.isOK()) return status;
			String response = solverProcess.sendAndListen("ASSERT " + translate(sexpr) + " ;\n");
			if (response.contains(errorIndication)) {
				return smtConfig.responseFactory.error(response);
			}
			return status;
		} catch (IOException e) {
			return status=smtConfig.responseFactory.error("Failed to assert expression: " + e + " " + sexpr, sexpr.pos());
		} catch (VisitorException e) {
			return status=smtConfig.responseFactory.error(e.getMessage(),null); // FIXME location
		}
	}

	@Override
	public IResponse check_sat() {
		IResponse res;
		status = super.check_sat();
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
			status = super.pop(number);
			if (!status.isOK()) return status;
			if (number == 0) return status=smtConfig.responseFactory.success();
			while (number-- > 0) {
				String response = solverProcess.sendAndListen("POP;\n");
				if (response.contains(errorIndication)) {
					return smtConfig.responseFactory.error(response);
				}
			}
			return status;
		} catch (IOException e) {
			return status=smtConfig.responseFactory.error("Failed to execute pop: " + e);
		}
	}

	@Override
	public IResponse push(int number) {
		try {
			status = super.push(number);
			if (!status.isOK()) return status;
			if (number == 0) return status=smtConfig.responseFactory.success();
			while (number-- > 0) {
				String response = solverProcess.sendAndListen("PUSH;\n");
				if (response.contains(errorIndication)) {
					return smtConfig.responseFactory.error(response);
				}
			}
			return status=smtConfig.responseFactory.success();
		} catch (IOException e) {
			return status=smtConfig.responseFactory.error("Failed to execute push: " + e);
		}
	}

	@Override
	public IResponse set_logic(String logicName, /*@Nullable*/ IPos pos) {
		
//		try {
			boolean lSet = logicSet;
			status = super.set_logic(logicName,pos);
			if (!status.isOK()) return status;
			// FIXME - discrimninate among logics
			if (lSet) {
				return status=smtConfig.responseFactory.error("Logic is already set");
//				String response = solverProcess.sendAndListen("POPTO 0;\n");
//				if (response.contains(errorIndication)) {
//					return smtConfig.responseFactory.error(response);
//				}
//				push(1); // FIXME - should this be here? check for errors?
			}
			return status;
//		} catch (IOException e) {
//			return status=smtConfig.responseFactory.error("Failed to execute set_logic: " + e);
//		}

	}

	@Override
	public IResponse set_option(IKeyword key, IAttributeValue value) {
		status = super.set_option(key,value);
		return status;
	}

	@Override
	public IResponse get_option(IKeyword key) {
		status = super.get_option(key);
		return status;
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
			return smtConfig.responseFactory.stringLiteral("Unspecified"); // FIXME
		} else if (":version".equals(option)) {
			return smtConfig.responseFactory.stringLiteral(Utils.VERSION_VALUE); // FIXME
		} else if (":name".equals(option)) {
			return smtConfig.responseFactory.stringLiteral("CVC3");
		} else {
			return smtConfig.responseFactory.unsupported();
		}
	}
	
	
	@Override
	public IResponse declare_fun(Ideclare_fun cmd){
		try {
			// FIXME - not allowed to have Boolean types
			if (!logicSet) {
				return status=smtConfig.responseFactory.error("The logic must be set before a declare-fun command is issued");
			}
			status = super.declare_fun(cmd);
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
			return status=smtConfig.responseFactory.error("Failed to execute set_logic: " + e);
		} catch (IVisitor.VisitorException e) {
			return status=smtConfig.responseFactory.error("Failed to execute set_logic: " + e);
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
		 * (or p q r ...)	(p OR q)  // FIXME > 2 args
		 * (and p q r ...)	(p AND q) // FIXME > 2 args
		 * (not p)			(NOT p)
		 * (=> p q r ...)	(p => q) // FIXME > 2 args
		 * (xor p q r ...)	(p XOR q) // FIXME > 2 args
		 * (= p q r ...)	(p <=> q)   - formulas // FIXME > 2 args
		 * (= p q r ...)	(p = q)   - terms // FIXME - more than 2 args
		 * (distinct p q r)	????   - formulas FIXME 
		 * (distinct p q r)	(DISTINCT p q r ... )   - terms  
		 * true				TRUE
		 * false			FALSE
		 * (ite b p q)		(IF b THEN p ELSE q ENDIF)
		 * 
		 */
		
		fcnNames.put("or","OR");				// >2 arguments ?? for cvc (left-assoc)
		fcnNames.put("and","AND");				// >2 arguments ?? for cvc (left-assoc)
		fcnNames.put("not","NOT");
		fcnNames.put("=>","=>");				// >2 arguments ?? for cvc (right-assoc)
		fcnNames.put("xor","XOR");				// >2 arguments ?? for cvc (left-assoc)
		fcnNames.put("=","="); // <=> for formula 	// >2 arguments ?? for cvc (chainable)
		fcnNames.put("distinct","DISTINCT"); // XOR for formula// >2 arguments ?? for cvc (pairwise)
		fcnNames.put("true","TRUE");
		fcnNames.put("false","FALSE");
		fcnNames.put("ite","IF");			// special in cvc  IF ... THEN ... ELSE ... FI
		fcnNames.put("+","+");				// >2 arguments ?? for cvc (left-assoc)
		fcnNames.put("-","-");				// >2 arguments ?? for cvc (left-assoc)
		fcnNames.put("*","*");				// >2 arguments ?? for cvc (left-assoc)
		fcnNames.put(">",">");				// >2 arguments ?? for cvc (left-assoc)		
		fcnNames.put(">=",">=");			// >2 arguments ?? for cvc (chainable)
		fcnNames.put("<","<");				// >2 arguments ?? for cvc (chainable)
		fcnNames.put("<=","<=");			// >2 arguments ?? for cvc (chainable)
		
		fcnNames.put("forall","FORALL");
		fcnNames.put("exists","EXISTS");
		fcnNames.put("let","LET");
	}
	

	/* Yices ids:
	 * 		FIXME - not  defined what Yices ids can be made of
	 */
	
	static public class Translator extends IVisitor.NullVisitor<String> {
		boolean isFormula = true;
		final private Map<IExpr,ISort> typemap;
		final private SMT.Configuration smtConfig;
		
		public Translator(Map<IExpr,ISort> typemap, SMT.Configuration smtConfig) {
			this.typemap = typemap;
			this.smtConfig = smtConfig;
		}

		@Override
		public String visit(IDecimal e) throws IVisitor.VisitorException {
			throw new VisitorException("The CVC solver cannot handle decimal literals", (IPos)e);
		}

		@Override
		public String visit(IStringLiteral e) throws IVisitor.VisitorException {
			throw new VisitorException("The CVC solver cannot handle string literals", (IPos)e);
		}

		@Override
		public String visit(INumeral e) throws IVisitor.VisitorException {
			return e.value().toString();
		}

		@Override
		public String visit(IBinaryLiteral e) throws IVisitor.VisitorException {
			// CVC prefix is 0bin - LSB is on right, MSB on left
			throw new VisitorException("Did not expect a Binary literal in an expression to be translated", (IPos)e);
		}

		@Override
		public String visit(IHexLiteral e) throws IVisitor.VisitorException {
			// CVC prefix is 0hex - LSB is on right, MSB on left
			throw new VisitorException("Did not expect a Hex literal in an expression to be translated", (IPos)e);
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
			infix.addAll(Arrays.asList(new String[]{"OR","AND","+","*"}));
		}

		@Override
		public String visit(IFcnExpr e) throws IVisitor.VisitorException {
			boolean resultIsFormula = this.isFormula;
			Iterator<IExpr> iter = e.args().iterator();
			if (!iter.hasNext()) throw new VisitorException("Did not expect an empty argument list", (IPos)e);
			String oldName = e.head().toString();
			String newName = e.head().accept(this);
			int length = e.args().size();
			StringBuilder sb = new StringBuilder();
			try {
				// Determine if the arguments are formulas or terms
				if (resultIsFormula) {
					if (newName != null && logicNames.contains(newName)) {
						// Propositional boolean item
						this.isFormula = true;
					} else {
						IExpr arg = e.args().get(e.args().size() <= 1 ? 0 : 1); // Use argument 1 for ite's sake
						ISort sort = typemap.get(arg);
						if (sort == null) {
							throw new VisitorException("INTERNAL ERROR: Encountered an un-sorted expression node: " + smtConfig.defaultPrinter.toString(arg),arg.pos());
						}
						if (sort.isBool()) {
							// Some functions can take both bool and non-bool arguments:
							//   EQ NEQ DISTINCT ite
							this.isFormula = resultIsFormula;
							if ("EQ".equals(newName)) newName = "IFF";
						} else {
							// Arguments must be terms
							this.isFormula = false;
						}
					}
				} else {
					this.isFormula = false;
				}

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
				} else if (newName.equals("=")) {
					newName = isFormula ? "<=>" : "=";
					sb.append(remove_chainable(newName,length,iter));
				} else if (newName.equals("XOR")) {
					sb.append(remove_leftassoc(newName,length,iter));
				} else if (newName.equals("NOT")) {
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
				} else if (oldName.equals("ite")) {
					// FIXME - terms only
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
				} else {
					// usual functional notation
					sb.append(oldName);
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
			// FIXME - need to check what acharacters are allowed in a CVC name
			String oldName = e.value();
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
			throw new VisitorException("Did not expect a Keyword in an expression to be translated",(IPos)e);
		}

		@Override
		public String visit(IError e) throws IVisitor.VisitorException {
			throw new VisitorException("Did not expect a Error token in an expression to be translated",(IPos)e);
}

		@Override
		public String visit(IParameterizedIdentifier e) throws IVisitor.VisitorException {
			// TODO Auto-generated method stub
			return null;
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
				String sort = s.family().accept(this);
				if ("Int".equals(sort)) return "INT";
				if ("Real".equals(sort)) return "REAL";
				return sort; // FIXME
				//throw new UnsupportedOperationException("CVC visit-ISort.IExpression");
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
