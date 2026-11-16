package org.smtlib.test;

import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.smtlib.IExpr;
import org.smtlib.ILogic;
import org.smtlib.ITheory;
import org.smtlib.SMT;

/**
 * The expression factory creates logic and theory nodes (#163 item 3), as the parser does. Stays a JUnit
 * test: the factory is API, with no script form.
 */
public class LogicTheoryFactoryTest {

    private final SMT.Configuration config = new SMT().smtConfig;
    private final IExpr.IFactory f = config.exprFactory;

    @Test
    public void logic() {
        IExpr.IAttribute<?> note = f.attribute(f.keyword(":notes"), f.unquotedString("a logic"));
        ILogic logic = f.logic(f.symbol("MyLogic"), List.of(note));
        Assert.assertEquals("MyLogic", logic.logicName().value());
        Assert.assertEquals(List.of(note), logic.attributeList());
        Assert.assertSame(note, logic.attributes().get(f.keyword(":notes")));
        Assert.assertEquals("(logic MyLogic :notes \"a logic\")", config.defaultPrinter.toString(logic));
    }

    @Test
    public void theory() {
        IExpr.IAttribute<?> note = f.attribute(f.keyword(":notes"), f.unquotedString("a theory"));
        ITheory theory = f.theory(f.symbol("MyTheory"), List.of(note));
        Assert.assertEquals("MyTheory", theory.theoryName().value());
        Assert.assertEquals(List.of(note), theory.attributeList());
        Assert.assertEquals("(theory MyTheory :notes \"a theory\")", config.defaultPrinter.toString(theory));
    }
}
