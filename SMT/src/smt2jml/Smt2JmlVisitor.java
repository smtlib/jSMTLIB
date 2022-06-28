package smt2jml;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.smtlib.IAccept;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IExists;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IForall;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.command.C_assert;
import org.smtlib.command.C_declare_const;
import org.smtlib.command.C_declare_fun;
import org.smtlib.command.C_declare_sort;
import org.smtlib.sexpr.Printer;
import org.smtlib.sexpr.Utils;

public class Smt2JmlVisitor extends Printer {

  private static Map<String, String> binaryOpsMap = new HashMap<>();
  private static Map<String, String> unaryOpsMap = new HashMap<>();
  private static Set<String> methods = new HashSet<>();
  private static int loopInvariantCount = 0;

  static {
    binaryOpsMap.put("or", "||");
    binaryOpsMap.put("and", "&&");
    binaryOpsMap.put("=>", "==>");
    binaryOpsMap.put("<", "<");
    binaryOpsMap.put("<=", "<=");
    binaryOpsMap.put(">", ">");
    binaryOpsMap.put(">=", ">=");
    binaryOpsMap.put("+", "+");
    binaryOpsMap.put("/", "/");
    binaryOpsMap.put("*", "*");
    binaryOpsMap.put("-", "-");
    binaryOpsMap.put("%", "%");
    binaryOpsMap.put("=", "==");
    binaryOpsMap.put("!=", "!=");
    unaryOpsMap.put("not", "!");
    unaryOpsMap.put("-", "-");
  }

  /** indent and alignment */
  private int lmargin = 0;
  private final int indentWidth = 2;

  private void indent() {
    lmargin += indentWidth;
  }

  private void undent() {
    lmargin -= indentWidth;
    if (lmargin < 0) {
      lmargin = 0;
    }
  }

  private void returnAndAlign() throws IOException {
    w.append("\n");
    for (int i = 0; i < lmargin; ++i) {
      w.append(" ");
    }
  }

  private void returnAndIndent() throws IOException {
    indent();
    returnAndAlign();
  }

  private void returnAndUndent() throws IOException {
    undent();
    returnAndAlign();
  }

  public Smt2JmlVisitor(final Writer w) {
    super(w);
  }

  @Override
  public Void visit(final IAttribute<?> e) throws VisitorException {
    return null;
  }

  @Override
  public Void visit(final IFcnExpr e) throws IVisitor.VisitorException {
    try {
      final String id = e.head().headSymbol().value();
      String sep = "";
      if (unaryOpsMap.containsKey(id)) {
        e.head().accept(this);
        for (final IExpr a : e.args()) {
          if (a != null) {
            a.accept(this);
          } else {
            w.append("???");
          }
        }
      } else if (binaryOpsMap.containsKey(id)) {
        w.append("(");
        e.args().get(0).accept(this);
        e.head().accept(this);
        e.args().get(1).accept(this);
        w.append(")");
      } else {
        e.head().accept(this);
        w.append("(");
        for (final IExpr a : e.args()) {
          w.append(sep);
          if (a != null) {
            a.accept(this);
          } else {
            w.append("???");
          }
          sep = ", ";
        }
        w.append(")");
      }
    } catch (final IOException ex) {
      throw new IVisitor.VisitorException(ex, e.pos());
    }
    return null;
  }

  @Override
  public Void visit(final IForall e) throws IVisitor.VisitorException {
    try {
      w.append("\\" + Utils.FORALL + " ");
      String sep = "";
      for (final IDeclaration a : e.parameters()) {
        w.append(sep);
        a.accept(this);
        sep = ", ";
      }
      w.append(";\n");
      w.append("  @                   ");
      e.expr().accept(this);
    } catch (final IOException ex) {
      throw new IVisitor.VisitorException(ex, e.pos());
    }
    return null;
  }

  @Override
  public Void visit(final IExists e) throws IVisitor.VisitorException {
    try {
      w.append("\\" + Utils.EXISTS + " ");
      String sep = "";
      for (final IDeclaration a : e.parameters()) {
        w.append(sep);
        a.accept(this);
        sep = ", ";
      }
      w.append(";\n");
      w.append("  @                   ");
      e.expr().accept(this);
    } catch (final IOException ex) {
      throw new IVisitor.VisitorException(ex, e.pos());
    }
    return null;
  }

  @Override
  public Void visit(final IDeclaration e) throws IVisitor.VisitorException {
    try {
      e.sort().accept(this);
      w.append(" ");
      e.parameter().accept(this);
    } catch (final IOException ex) {
      throw new VisitorException(ex, e.pos());
    }
    return null;
  }

  @Override
  public Void visit(final ISymbol e) throws IVisitor.VisitorException {
    final String sym = e.value();
    try {
      if (unaryOpsMap.containsKey(sym)) {
        w.append(unaryOpsMap.get(sym));
        return null;
      }
      if (binaryOpsMap.containsKey(sym)) {
        w.append(" " + binaryOpsMap.get(sym) + " ");
        return null;
      }
      if (sym.endsWith("_final")) {
        w.append(sym.replace("_final", ""));
        return null;
      } else if (sym.endsWith("length")) {
        w.append(sym.replace("length", ".length"));
        return null;
      }
      switch (sym) {
        case "Int":
          w.append("int");
          return null;
        case "Bool":
          w.append("boolean");
          return null;
        default:
          w.append(e.toString());
          return null;
      }
    } catch (final IOException ex) {
      throw new IVisitor.VisitorException(ex);
    }
  }

  @Override
  public Void visit(final ICommand e) throws IVisitor.VisitorException {
    if (e instanceof C_declare_fun) {
      visitDeclareFun((C_declare_fun) e);
      return null;
    } else if (e instanceof C_declare_sort) {
      visitDeclareSort((C_declare_sort) e);
      return null;
    } else if (e instanceof C_assert) {
      visitAssert((C_assert) e);
      return null;
    }
    super.visit(e);
    return null;
  }

  private void visitAssert(final C_assert that) {
    try {
      w.append("/*[" + ++loopInvariantCount + "]*/");
      final IExpr formula = that.expr();
      w.append("/*@\n");
      w.append("  @ loop_invariant ");
      formula.accept(this);
      w.append(";");
      w.append("\n  @*/");
    } catch (final IOException e) {
      error(e.getMessage());
    } catch (final VisitorException e) {
      error(e.getMessage());
    }
  }

  private void visitDeclareSort(final C_declare_sort that) {
    if (!Smt2JmlPreprocessor.usedSymbols.contains(that.sortSymbol().toString())) {
      return;
    }
    try {
      w.append("public class ");
      that.sortSymbol().accept(this);
      w.append(" {");
      returnAndIndent();
      w.append("public ");
      that.sortSymbol().accept(this);
      w.append(" (");
      char paramName = 'a';
      String sep = "";
      for (int i = 0; i < that.arity().intValue(); ++i) {
        w.append(sep);
        w.append("/*TYPE*/ "); // The type of each parameter is not defined.
        w.append(paramName++);
        sep = ", ";
      }
      w.append(") {}");
      returnAndUndent();
      w.append("}");
    } catch (final IOException e) {
      error(e.getMessage());
    } catch (final VisitorException e) {
      error(e.getMessage());
    }
  }

  private void visitDeclareFun(final C_declare_fun that) {
    if (!Smt2JmlPreprocessor.usedSymbols.contains(that.symbol().toString())) {
      return;
    }
    if (that instanceof C_declare_const) {
      visitDeclareConst((C_declare_const) that);
      return;
    }
    try {
      methods.add(that.symbol().value());
      w.append("//@ public pure model ");
      that.resultSort().accept(this);
      w.append(" ");
      that.symbol().accept(this);
      w.append("(");
      char paramName = 'a';
      String sep = "";
      for (final ISort s : that.argSorts()) {
        w.append(sep);
        s.accept(this);
        w.append(" ");
        w.append(paramName++);
        sep = ", ";
      }
      w.append(");");
    } catch (final IOException e) {
      error(e.getMessage());
    } catch (final VisitorException e) {
      error(e.getMessage());
    }
  }

  private void visitDeclareConst(final C_declare_const that) {
    try {
      if (that.symbol().toString().endsWith("_init")) {
        w.append("//@ ghost final ");
        that.resultSort().accept(this);
        w.append(" ");
        that.symbol().accept(this);
        w.append(" = ");
        w.append(that.symbol().toString().replace("_init", ";"));
      } else {
        w.append("//@ public ghost model ");
        that.resultSort().accept(this);
        w.append(" ");
        that.symbol().accept(this);
        w.append(";");
      }
    } catch (final IOException e) {
      error(e.getMessage());
    } catch (final VisitorException e) {
      error(e.getMessage());
    }
  }

  /**
   * Returns the argument as a String using a Printer of the same type as the receiver, but does not
   * modify the receiver.
   */
  @Override
  public <T extends IAccept> String toString(final T expr) {
    try {
      if (expr == null) {
        throw new IVisitor.VisitorException(new Throwable("expr is null"));
      }
      final StringWriter sw = new StringWriter();
      expr.accept(new Smt2JmlVisitor(sw));
      return sw.toString();
    } catch (final IVisitor.VisitorException e) {
      return "<<ERROR: " + e.getMessage() + ">>";
    }
  }
}
