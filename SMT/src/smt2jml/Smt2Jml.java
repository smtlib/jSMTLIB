package smt2jml;

import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Paths;
import org.smtlib.CharSequenceReader;
import org.smtlib.ICommand;
import org.smtlib.IExpr;
import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.SMT;

public class Smt2Jml {

  public static void main(final String... args) {
    final SMT smt = new SMT();


    try {
      // Parsing from a string
      final IExpr.IFactory efactory = smt.smtConfig.exprFactory;
      final String str = new String(
          Files.readAllBytes(Paths.get("/Users/koja/UCF/Research/rapidOutput/out.smt2")));
      final ISource source = smt.smtConfig.smtFactory
          .createSource(new CharSequenceReader(new java.io.StringReader(str)), null);
      final IParser parser = smt.smtConfig.smtFactory.createParser(smt.smtConfig, source);
      smt.smtConfig.defaultPrinter = new Smt2JmlVisitor(new StringWriter());
      while (!parser.isEOD()) {
        final ICommand command0 = parser.parseCommand();
        System.out.println(smt.smtConfig.defaultPrinter.toString(command0));
      }


    } catch (final java.io.IOException e) {
      // Can happen if the ISource is reading from a file
    } catch (final IParser.ParserException e) {
      System.out.println(e.getMessage());
    }
  }

}
