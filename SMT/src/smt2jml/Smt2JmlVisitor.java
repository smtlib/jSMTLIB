package smt2jml;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import org.smtlib.IAccept;
import org.smtlib.IExpr;
import org.smtlib.IExpr.IAttribute;
import org.smtlib.IExpr.IFcnExpr;
import org.smtlib.IVisitor;
import org.smtlib.sexpr.Printer;

public class Smt2JmlVisitor extends Printer {

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
      w.append("(");
      e.head().accept(this);
      for (final IExpr a : e.args()) {
        w.append(" ");
        if (a != null) {
          a.accept(this);
        } else {
          w.append("???");
        }
      }
      w.append(")");
    } catch (final IOException ex) {
      throw new IVisitor.VisitorException(ex, e.pos());
    }
    return null;
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
