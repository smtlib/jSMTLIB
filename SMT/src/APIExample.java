import org.smtlib.*;
import org.smtlib.command.C_declare_fun;
import org.smtlib.impl.Script;

public class APIExample {

	public static void main(String... args) {
		SMT smt = new SMT();
		
		
		try {
			// Parsing from a string
			IExpr.IFactory efactory = smt.smtConfig.exprFactory;
			ISource source = smt.smtConfig.smtFactory.createSource(new CharSequenceReader(new java.io.StringReader("(set-logic QF_UF)(declare-fun p () Bool)")),null);
			IParser parser = smt.smtConfig.smtFactory.createParser(smt.smtConfig,source);
			ICommand command1 = parser.parseCommand();
			ICommand command2 = parser.parseCommand();
			if (!parser.isEOD()) {
				System.out.println("Expected parser to be at EOD");
			}
			
			// Parsing with an error
			source = smt.smtConfig.smtFactory.createSource(new CharSequenceReader(new java.io.StringReader("(assert )")),null);
			parser = smt.smtConfig.smtFactory.createParser(smt.smtConfig,source);
			ICommand c = parser.parseCommand();
			System.out.println(c == null ? "BAD COMMAND" : "NON_NULL COMMAND");
			
			// Constructing ASTs directly
			IExpr.ISymbol p = efactory.symbol("p");
			IExpr notp = efactory.fcn(efactory.symbol("not"),p);
			IExpr and = efactory.fcn(efactory.symbol("and"),p,notp);
			ICommand command3 = new org.smtlib.command.C_assert(and);
			ICommand command4 = new org.smtlib.command.C_exit();
			
			// Printing an AST
			IPrinter printer = smt.smtConfig.defaultPrinter;
			System.out.println(printer.toString(and));
			System.out.println(printer.toString(command1));
			System.out.println(printer.toString(command3));
			
			// Assemble a script
			ICommand.IScript script = new org.smtlib.impl.Script();
			script.commands().add(command1);
			script.commands().add(command2);
			script.commands().add(command3);
			script.commands().add(command4);
			
			// Execute the script
			ISolver solver = new org.smtlib.solvers.Solver_z3(smt.smtConfig,"C:/cygwin/home/dcok/mybin/z3.exe");
			solver.start();
			IResponse response = script.execute(solver);
			System.out.println(printer.toString(response));

			// Type-checking a script
			IExpr.ISymbol q = efactory.symbol("q");
			script = new org.smtlib.impl.Script();
			script.commands().add(command1);
			script.commands().add(command2);
			script.commands().add(new org.smtlib.command.C_assert(q));
			script.commands().add(command4);			
			solver = new org.smtlib.solvers.Solver_z3(smt.smtConfig,"C:/cygwin/home/dcok/mybin/z3.exe");
			solver.start();
			response = script.execute(solver);
			System.out.println(printer.toString(response));
			
			
			// Execute commands directly
			// THIS API WILL BE CHANGING
			ISort.IFactory sortfactory = smt.smtConfig.sortFactory;
			ISort boolsort = sortfactory.createSortExpression(efactory.symbol("Bool"));
			solver = new org.smtlib.solvers.Solver_z3(smt.smtConfig,"C:/cygwin/home/dcok/mybin/z3.exe");
			solver.start();
			IResponse r = solver.set_logic("QF_UF",null);
			r = solver.declare_fun(new C_declare_fun(p,new java.util.LinkedList<ISort>(),boolsort));
			r = solver.assertExpr(and);
			r = solver.check_sat();
			System.out.println(printer.toString(r));
			// solver.start()?  solver.exit()????, restarting solver?
			// comment on toString directly on ASTs?t
			
			// typechecking?
			
			
		} catch (java.io.IOException e) {
			// Can happen if the ISource is reading from a file
		} catch (IParser.ParserException e) {
			System.out.println(e.getMessage());
		}
	}
}
