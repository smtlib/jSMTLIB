package org.smtlib.command;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import org.smtlib.IParser.ParserException;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.IVisitor;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.impl.Command;
import org.smtlib.impl.Response;
import org.smtlib.sexpr.Parser;
import org.smtlib.sexpr.Printer;

public class C_declare_nat extends Command {

  public static final String javaDir = "/Users/koja/UCF/Research/declare-nat/";

  /** The command name */
  public static final String commandName = "declare-nat";

  public C_declare_nat() {}

  /** Parses the arguments of the command, producing a new command instance */
  static public /* @Nullable */ C_declare_nat parse(final Parser p)
      throws IOException, ParserException {
    p.parseExpr();
    while (!p.isRP()) {
      p.parseExpr();
    }
    return new C_declare_nat();
  }

  @Override
  public IResponse execute(final ISolver solver) {
    return (new Response.Factory(solver.smt())).unknown();
  }

  @Override
  public <T> T accept(final IVisitor<T> v) throws VisitorException {
    return v.visit(this);
  }

  /** The command name */
  @Override
  public String commandName() {
    return commandName;
  }

  /** Writes out the command in S-expression syntax using the given printer */
  public void write(final Printer p) throws IOException, IVisitor.VisitorException {
    final String natJava = new String(Files.readAllBytes(Paths.get(javaDir + "Nat.java")));
    p.writer().append(natJava);
  }


}
