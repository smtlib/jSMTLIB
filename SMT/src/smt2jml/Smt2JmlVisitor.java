package smt2jml;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.HashMap;
import java.util.Map;
import org.smtlib.IAccept;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IDeclaration;
import org.smtlib.IExpr.IExists;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IExpr.IForall;
import org.smtlib.IExpr.ILiteral;
import org.smtlib.IExpr.IQualifiedIdentifier;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.IVisitor;
import org.smtlib.impl.SMTExpr.FcnExpr;
import org.smtlib.impl.SMTExpr.Symbol;
import org.smtlib.sexpr.Printer;
import org.smtlib.sexpr.Utils;

public class Smt2JmlVisitor extends Printer {

  private static Map<String, String> opsMap = createOpsMap();

  private static Map<String, String> createOpsMap() {
    final Map<String, String> map = new HashMap<>();
    map.put("or", "||");
    map.put("and", "&&");
    map.put("=>", "==>");
    map.put("<", "<");
    map.put("<=", "<=");
    map.put(">", ">");
    map.put(">=", ">=");
    map.put("+", "+");
    map.put("/", "/");
    map.put("*", "*");
    map.put("-", "-");
    map.put("%", "%");
    map.put("=", "==");
    map.put("!=", "!=");
    return map;
  }


  public Smt2JmlVisitor(final Writer w) {
    super(w);
    // TODO Auto-generated constructor stub
  }

  @Override
  public Void visit(final IAttribute<?> e) throws VisitorException {
    // TODO Auto-generated method stub
    return null;
  }

  @Override
  public Void visit(final IFcnExpr e) throws IVisitor.VisitorException {
    try {
      if (!isBinaryOp(e.head())) {
        w.append(e.head().toString());
        if (!e.args().get(0).toString().equals("main_end")) {
          w.append('[');
          w.append(e.args().get(0).toString());
          w.append(']');
        }
        return null;
      }
      final IExpr lhs = e.args().get(0);
      final IExpr rhs = e.args().get(1);
      if (!isSymbolOrLiteral(lhs) && !isSymbolOrLiteral(rhs)) {
        w.append("(");
      }
      lhs.accept(this);
      e.head().accept(this);
      rhs.accept(this);
      if (!isSymbolOrLiteral(lhs) && !isSymbolOrLiteral(rhs)) {
        w.append(")");
      }
    } catch (

    final IOException e1) {
      e1.printStackTrace();
    }
    return null;
  }

  private boolean isSymbolOrLiteral(final IExpr expr) {
    return expr instanceof ISymbol || expr instanceof ILiteral;
  }

  private boolean isBinaryOp(final IQualifiedIdentifier identifier) {
    if (identifier instanceof Symbol) {
      final Symbol sym = (Symbol) identifier;
      return opsMap.containsKey(sym.value());
    }
    return false;
  }

  @Override
  public Void visit(final IForall e) throws IVisitor.VisitorException {
    try {
      w.append("(\\" + Utils.FORALL + " ");
      boolean isFirstDec = true;
      for (final IDeclaration a : e.parameters()) {
        if (!isFirstDec) {
          w.append(", ");
        }
        a.accept(this);
        isFirstDec = false;
      }
      w.append("; ");
      if (e.expr() instanceof FcnExpr) {
        final FcnExpr fcnExpr = (FcnExpr) e.expr();
        fcnExpr.args().get(0).accept(this);
        w.append("; ");
        fcnExpr.args().get(1).accept(this);
      }
      w.append(")");
    } catch (final IOException ex) {
      throw new IVisitor.VisitorException(ex, e.pos());
    }
    return null;
  }

  @Override
  public Void visit(final IExists e) throws IVisitor.VisitorException {
    try {
      w.append("(\\" + Utils.EXISTS + " ");
      boolean isFirstDec = true;
      for (final IDeclaration a : e.parameters()) {
        if (!isFirstDec) {
          w.append(", ");
        }
        a.accept(this);
        isFirstDec = false;
      }
      w.append("; ");
      if (e.expr() instanceof FcnExpr) {
        final FcnExpr fcnExpr = (FcnExpr) e.expr();
        fcnExpr.args().get(0).accept(this);
        w.append("; ");
        fcnExpr.args().get(1).accept(this);
      }
      w.append(")");
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
    try {
      if (opsMap.containsKey(e.value())) {
        w.append(" " + opsMap.get(e.value()) + " ");
        return null;
      }
      switch (e.value()) {
        case "Int":
          w.append("int");
          break;
        default:
          w.append(e.toString());
          break;
      }
    } catch (final IOException ex) {
      throw new IVisitor.VisitorException(ex);
    }
    return null; // FIXME - need an encoding - this gives the original text
  }

  /**
   * Returns the argument as a String using a Printer of the same type as the receiver, but does not
   * modify the receiver.
   */
  @Override
  public <T extends IAccept> String toString(final T expr) {
    try {
      final StringWriter sw = new StringWriter();
      expr.accept(new Smt2JmlVisitor(sw));
      return sw.toString();
    } catch (final IVisitor.VisitorException e) {
      return "<<ERROR: " + e.getMessage() + ">>";
    }
  }

}
