package smt2jml;

import java.io.IOException;
import java.io.PrintStream;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import org.smtlib.CharSequenceReader;
import org.smtlib.ICommand;
import org.smtlib.IParser;
import org.smtlib.ISource;
import org.smtlib.IVisitor.VisitorException;
import org.smtlib.SMT;

public class Smt2Jml {

  public static final Path outputDir = Paths.get("/Users/koja/UCF/Research/output/");

  public static void main(final String... args) {
    smt2Jml(outputDir.resolve("loop_inv.smt2"), System.out);
  }

  public static void smt2Jml(final Path input, final PrintStream output) {
    final SMT smt = new SMT();


    try {
      smt.smtConfig.log.clearListeners(); // Don't output error log to System.out
      String fileString = new String(Files.readAllBytes(input));
      fileString = prepare(fileString);
      final ISource source = smt.smtConfig.smtFactory
          .createSource(new CharSequenceReader(new java.io.StringReader(fileString)), null);
      IParser parser = smt.smtConfig.smtFactory.createParser(smt.smtConfig, source);
      final Smt2JmlPreprocessor preprocessor = new Smt2JmlPreprocessor();
      while (!parser.isEOD()) {
        final ICommand command = parser.parseCommand();
        if (command != null) {
          command.accept(preprocessor);
        }
      }
      parser = smt.smtConfig.smtFactory.createParser(smt.smtConfig, source);
      smt.smtConfig.defaultPrinter = new Smt2JmlVisitor(new StringWriter());
      while (!parser.isEOD()) {
        final ICommand command = parser.parseCommand();
        if (command != null) {
          output.println(smt.smtConfig.defaultPrinter.toString(command));
        }
      }
    } catch (final java.io.IOException e) {
      // Can happen if the ISource is reading from a file
      System.err.println(e.getMessage());
    } catch (final IParser.ParserException e) {
      System.err.println(e.getMessage());
    } catch (final java.nio.file.FileSystemNotFoundException e) {
      System.err.println(e.getMessage());
    } catch (final VisitorException e) {
      System.err.println(e.getMessage());
    }
  }

  private static String prepare(final String fileString) throws IOException {
    return fileString.replace("'", ""); // remove single quotes
  }

}
