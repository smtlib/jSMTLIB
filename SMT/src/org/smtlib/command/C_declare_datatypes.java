package org.smtlib.command;

import java.io.IOException;
import org.smtlib.ICommand.Ideclare_datatypes;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.impl.Command;
import org.smtlib.impl.SMTExpr;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

public class C_declare_datatypes extends Command implements Ideclare_datatypes {

  /** The command name */
  public static final String commandName = "declare-datatypes";

  /** The name of the function being declared */
  protected ISymbol fcnName;

  /** The command name */
  @Override
  public String commandName() {
    return commandName;
  }

  @Override
  public ISymbol symbol() {
    return fcnName;
  }

  /** Constructs a command instance from its components */
  public C_declare_datatypes(final ISymbol symbol) {
    this.fcnName = symbol;
  }

  /** Writes the command in the syntax of the given printer */
  public void write(final Printer p) throws IOException, IVisitor.VisitorException {
    p.writer().append("(" + commandName + " ");
    symbol().accept(p);
    p.writer().append(")");

  }

  /** Parses the arguments of the command, producing a new command instance */
  static public /* @Nullable */ C_declare_datatypes parse(final Parser p) throws ParserException {
    // /* @Nullable */ final ISymbol symbol = p.parseSymbol();
    // if (symbol == null) {
    // return null;
    // }
    return new C_declare_datatypes(new SMTExpr.Symbol("aaaa"));
  }

  @Override
  public <T> T accept(final IVisitor<T> v) throws IVisitor.VisitorException {
    return v.visit(this);
  }

  @Override
  public IResponse execute(final ISolver solver) {
    return null;
  }

}
