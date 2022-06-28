package smt2jml;

import java.util.HashSet;
import java.util.Set;
import org.smtlib.ICommand;
import org.smtlib.IExpr.ISymbol;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.IVisitor.TreeVisitor;
import org.smtlib.command.C_assert;
import org.smtlib.command.C_declare_const;
import org.smtlib.command.C_declare_fun;
import org.smtlib.command.C_declare_sort;

public class Smt2JmlPreprocessor extends TreeVisitor<Void> {
  private boolean isAssertion = false;
  public static Set<String> usedSymbols = new HashSet<>();

  @Override
  public Void visit(final ISymbol e) throws VisitorException {
    if (isAssertion) {
      usedSymbols.add(e.toString());
    }
    return null;
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
    return null;
  }

  private void visitAssert(final C_assert that) {
    try {
      isAssertion = true;
      that.expr().accept(this);
      isAssertion = false;
    } catch (final VisitorException e) {
      System.err.println(e.getMessage());
    }
  }

  private void visitDeclareSort(final C_declare_sort that) {
    try {
      that.sortSymbol().accept(this);
      that.sortSymbol().accept(this);
    } catch (final VisitorException e) {
      System.err.println(e.getMessage());
    }
  }

  private void visitDeclareFun(final C_declare_fun that) {
    if (that instanceof C_declare_const) {
      visitDeclareConst((C_declare_const) that);
      return;
    }
    try {
      that.resultSort().accept(this);
      that.symbol().accept(this);
      for (final ISort s : that.argSorts()) {
        s.accept(this);
      }
    } catch (final VisitorException e) {
      System.err.println(e.getMessage());
    }
  }

  private void visitDeclareConst(final C_declare_const that) {
    try {
      that.resultSort().accept(this);
      that.symbol().accept(this);
    } catch (final VisitorException e) {
      System.err.println(e.getMessage());
    }
  }


}
