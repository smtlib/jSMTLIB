package org.smtlib.command;

import java.io.IOException;
import org.smtlib.ICommand.Iassert;
import org.smtlib.IExpr;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

public class C_assert_not extends Command implements Iassert {

  /** Constructs a command object given the expression to assert */
  public C_assert_not(final IExpr expr) {
    formula = expr;
  }

  /** Returns the asserted formula */
  @Override
  public IExpr expr() {
    return formula;
  }

  /** The command name */
  public static final String commandName = "assert-not";

  /** The command name */
  @Override
  public String commandName() {
    return commandName;
  }

  /** The formula to assert */
  protected IExpr formula;

  /** Writes out the command in S-expression syntax using the given printer */
  public void write(final Printer p) throws IOException, IVisitor.VisitorException {
    // p.writer().append("(" + commandName + " ");
    p.writer().append("//@ maintain ");
    formula.accept(p);
    p.writer().append(";");
  }

  /** Parses the arguments of the command, producing a new command instance */
  static public /* @Nullable */ C_assert_not parse(final Parser p)
      throws IOException, ParserException {
    final IExpr expr = p.parseExpr();
    if (expr == null) {
      return null;
    }
    return new C_assert_not(expr);
  }

  @Override
  public IResponse execute(final ISolver solver) {
    return solver.assertExpr(formula);
  }

  @Override
  public <T> T accept(final IVisitor<T> v) throws IVisitor.VisitorException {
    return v.visit(this);
  }
}
