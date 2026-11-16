package org.smtlib.test;

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IParser;
import org.smtlib.IResponse;
import org.smtlib.ISolver;
import org.smtlib.ISort;
import org.smtlib.IVisitor;
import org.smtlib.SMT;

/**
 * Type checking links each use of a function or constant to the identifier that declares it (#226). Each
 * case writes the script with markers, removed before parsing: {@code ‹decl›} marks a declaration, and
 * {@code «use:k»} a use that should be linked to the k-th declaration (0-based). Stays a JUnit test: the
 * links are API, not visible in output.
 */
public class DeclarationLinkApiTests {

    /** The script with the markers removed; the uses' positions, each with the index of its expected
     *  declaration; and the declarations' positions */
    private record Marked(String text, List<int[]> uses, List<Integer> decls) {}

    private static Marked mark(String s) {
        StringBuilder text = new StringBuilder();
        List<int[]> uses = new ArrayList<>();
        List<Integer> decls = new ArrayList<>();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c == '‹') {
                decls.add(text.length());
            } else if (c == '«') {
                int close = s.indexOf('»', i);
                String[] parts = s.substring(i + 1, close).split(":");
                uses.add(new int[] { text.length(), parts.length > 1 ? Integer.parseInt(parts[1]) : -1 });
                text.append(parts[0]);
                i = close;
            } else if (c != '›') {
                text.append(c);
            }
        }
        return new Marked(text.toString(), uses, decls);
    }

    /** Executes the script's commands on the test solver; returns the commands */
    private static List<ICommand> check(String text, boolean relax) throws Exception {
        SMT smt = new SMT();
        PrintStream sink = new PrintStream(OutputStream.nullOutputStream());
        smt.smtConfig.stdout = sink;
        smt.smtConfig.stderr = sink;
        smt.smtConfig.log.setChannels(sink, sink);
        smt.smtConfig.relax = relax;
        ISolver solver = smt.smtConfig.createSolver("test", null);
        solver.start();
        IParser p = smt.smtConfig.smtFactory.createParser(smt.smtConfig, smt.smtConfig.smtFactory.createSource(text, null));
        List<ICommand> commands = new ArrayList<>();
        while (!p.isEOD()) {
            ICommand cmd = p.parseCommand();
            if (cmd == null) continue;
            commands.add(cmd);
            IResponse r = cmd.execute(solver);
            Assert.assertFalse(text + ": " + smt.smtConfig.defaultPrinter.toString(r), r.isError());
        }
        return commands;
    }

    /** The identifier in the commands' expressions or sorts that starts at the given offset */
    private static IExpr.IIdentifier identifierAt(List<ICommand> commands, int offset) throws Exception {
        IExpr.IIdentifier[] found = new IExpr.IIdentifier[1];
        IVisitor.TreeVisitor<Void> v = new IVisitor.TreeVisitor<Void>() {
            @Override public Void visit(IExpr.ISymbol e) {
                if (e.pos() != null && e.pos().charStart() == offset) found[0] = e;
                return null;
            }
            @Override public Void visit(IExpr.IDeclaration d) throws IVisitor.VisitorException {
                d.parameter().accept(this);
                sortAt(d.sort(), offset, found);
                return null;
            }
            @Override public Void visit(IExpr.IPattern p) throws IVisitor.VisitorException {
                p.constructor().accept(this);
                return null;
            }
        };
        for (ICommand cmd : commands) {
            for (IExpr e : expressions(cmd)) e.accept(v);
            for (ISort srt : sorts(cmd)) sortAt(srt, offset, found);
        }
        Assert.assertNotNull("no identifier at " + offset, found[0]);
        return found[0];
    }

    /** Looks for the sort name at the offset in the sort */
    private static void sortAt(ISort s, int offset, IExpr.IIdentifier[] found) {
        if (s instanceof ISort.IParameter p) {
            if (p.symbol().pos() != null && p.symbol().pos().charStart() == offset) found[0] = p.symbol();
        } else if (s instanceof ISort.IApplication a) {
            if (a.family().pos() != null && a.family().pos().charStart() == offset) found[0] = a.family();
            for (ISort p : a.parameters()) sortAt(p, offset, found);
        }
    }

    private static List<ISort> sorts(ICommand cmd) {
        List<ISort> list = new ArrayList<>();
        if (cmd instanceof ICommand.Ideclare_fun f) {
            list.addAll(f.argSorts());
            list.add(f.resultSort());
        }
        if (cmd instanceof ICommand.Ideclare_const c) list.add(c.resultSort());
        if (cmd instanceof ICommand.Idefine_sort d) list.add(d.expression());
        if (cmd instanceof ICommand.Idefine_fun f) {
            for (IExpr.IDeclaration d : f.parameters()) list.add(d.sort());
            list.add(f.resultSort());
        }
        if (cmd instanceof ICommand.Ideclare_datatypes d) {
            for (ISort.IDatatype dt : d.datatypes()) {
                for (IExpr.IConstructor c : dt.constructors()) {
                    for (IExpr.ISelector sel : c.selectors()) list.add(sel.sort());
                }
            }
        }
        return list;
    }

    private static List<IExpr> expressions(ICommand cmd) {
        List<IExpr> list = new ArrayList<>();
        if (cmd instanceof ICommand.Iassert a) list.add(a.expr());
        if (cmd instanceof ICommand.Idefine_fun f) list.add(f.expression());
        if (cmd instanceof ICommand.Idefine_fun_rec f) list.add(f.expression());
        return list;
    }

    /** Checks the marked script: the i-th use is linked to the i-th declaration */
    private static void links(String marked) throws Exception {
        links(marked, false);
    }

    private static void links(String marked, boolean relax) throws Exception {
        Marked m = mark(marked);
        List<ICommand> commands = check(m.text(), relax);
        for (int[] u : m.uses()) {
            IExpr.IIdentifier use = identifierAt(commands, u[0]);
            IExpr.IIdentifier decl = use.declaration();
            Assert.assertNotNull("the use at " + u[0] + " has no declaration", decl);
            Assert.assertEquals("the use at " + u[0], (int) m.decls().get(u[1]), decl.pos().charStart());
        }
    }

    @Test
    public void declaredConstantAndFunction() throws Exception {
        links("(set-logic QF_UF)(declare-fun ‹p () Bool)(declare-fun ‹f (Bool) Bool)(assert («f:1» «p:0»))");
    }

    @Test
    public void declareConstAndDefineFun() throws Exception {
        links("(set-logic QF_LIA)(declare-const ‹x Int)(define-fun ‹g ((‹a Int)) Int (+ «a:2» «x:0»))(assert (> («g:1» 1) 0))");
    }

    @Test
    public void letAndShadowing() throws Exception {
        links("(set-logic QF_LIA)(declare-const ‹x Int)(assert (let ((‹x 1)) (> «x:1» 0)))(assert (> «x:0» 0))");
    }

    @Test
    public void quantifiedVariables() throws Exception {
        links("(set-logic ALL)(declare-fun ‹f (Int) Int)(assert (forall ((‹y Int)) (exists ((‹z Int)) (= («f:0» «y:1») «z:2»))))");
    }

    @Test
    public void recursiveFunction() throws Exception {
        links("(set-logic LIA)(define-fun-rec ‹h ((‹n Int)) Int (ite (<= «n:1» 0) 0 («h:0» (- «n:1» 1))))");
    }

    @Test
    public void redeclaredAfterPop() throws Exception {
        links("(set-logic QF_UF)(push 1)(declare-fun p () Bool)(pop 1)(declare-fun ‹p () Bool)(assert «p:0»)");
    }

    @Test
    public void overloadedTheorySymbolsLinkToTheirOwnDeclarations() throws Exception {
        Marked m = mark("(set-logic QF_LIA)(declare-const x Int)(assert (= («-» x) («-» x 1)))");
        List<ICommand> commands = check(m.text(), false);
        IExpr.IIdentifier unary = identifierAt(commands, m.uses().get(0)[0]).declaration();
        IExpr.IIdentifier binary = identifierAt(commands, m.uses().get(1)[0]).declaration();
        Assert.assertNotNull(unary);
        Assert.assertNotNull(binary);
        Assert.assertNotEquals("unary and binary - are different declarations",
                unary.pos().charStart(), binary.pos().charStart());
    }

    @Test
    public void declaredAndDefinedSorts() throws Exception {
        links("(set-logic ALL)(declare-sort ‹U 0)(define-sort ‹V () «U:0»)(declare-fun f («U:0») «V:1»)"
                + "(declare-const c «V:1»)(assert (forall ((x «U:0»)) (= (f x) c)))");
    }

    @Test
    public void sortParameter() throws Exception {
        links("(set-logic ALL)(define-sort ‹M (‹X) (Array «X:1» «X:1»))(declare-const m («M:0» Int))");
    }

    @Test
    public void datatypeParameter() throws Exception {
        links("(set-logic ALL)(declare-datatypes ((‹Pair 1)) ((par (‹T) ((pair (first «T:1») (second «T:1»))))))"
                + "(declare-const p («Pair:0» Int))(assert (= (first p) (second p)))");
    }

    @Test
    public void datatypeSort() throws Exception {
        links("(set-logic ALL)(declare-datatypes ((‹Pair 1)) ((par (T) ((pair (first T) (second T))))))"
                + "(declare-const p («Pair:0» Int))");
    }

    @Test
    public void matchConstructors() throws Exception {
        links("(set-logic ALL)(declare-datatypes ((L 0)) (((‹nil) (‹cons (hd Int) (tl L)))))(declare-const l L)"
                + "(assert (match l ((«nil:0» true) ((«cons:1» h t) false))))");
    }

    @Test
    public void signatureTableSymbolsShareADeclarationWithoutPosition() throws Exception {
        Marked m = mark("(set-logic QF_BV)(declare-const a (_ BitVec 8))(assert (= («bvadd» a a) («bvadd» a a)))");
        List<ICommand> commands = check(m.text(), false);
        IExpr.IIdentifier first = identifierAt(commands, m.uses().get(0)[0]).declaration();
        IExpr.IIdentifier second = identifierAt(commands, m.uses().get(1)[0]).declaration();
        Assert.assertNotNull(first);
        Assert.assertSame("one declaration for every use of bvadd", first, second);
        Assert.assertNull("the theory states bvadd only in prose", first.pos());
    }

    @Test
    public void indexedSortsShareADeclarationWithoutPosition() throws Exception {
        Marked m = mark("(set-logic QF_BV)(declare-const a (_ «BitVec» 8))(declare-const b (_ «BitVec» 8))");
        List<ICommand> commands = check(m.text(), false);
        IExpr.IIdentifier first = indexedSortAt(commands, m.uses().get(0)[0]);
        IExpr.IIdentifier second = indexedSortAt(commands, m.uses().get(1)[0]);
        Assert.assertNotNull(first.declaration());
        Assert.assertSame("one declaration for every use of BitVec", first.declaration(), second.declaration());
        Assert.assertNull("the theory states BitVec only in prose", first.declaration().pos());
    }

    /** The indexed sort (_ S ...) of a declare-const whose head symbol S starts at the offset */
    private static IExpr.IIdentifier indexedSortAt(List<ICommand> commands, int offset) {
        for (ICommand cmd : commands) {
            if (cmd instanceof ICommand.Ideclare_const c && c.resultSort() instanceof ISort.IApplication a
                    && a.family() instanceof IExpr.IParameterizedIdentifier p
                    && p.headSymbol().pos() != null && p.headSymbol().pos().charStart() == offset) {
                return a.family();
            }
        }
        throw new AssertionError("no indexed sort at " + offset);
    }

    @Test
    public void theorySymbolLinksIntoTheTheory() throws Exception {
        Marked m = mark("(set-logic QF_LIA)(declare-const x Int)(assert («>» x 0))");
        List<ICommand> commands = check(m.text(), false);
        IExpr.IIdentifier use = identifierAt(commands, m.uses().get(0)[0]);
        Assert.assertNotNull(use.declaration());
        Assert.assertNotSame("the declaration is in the theory, not the script",
                use.pos().source(), use.declaration().pos() == null ? null : use.declaration().pos().source());
    }
}
