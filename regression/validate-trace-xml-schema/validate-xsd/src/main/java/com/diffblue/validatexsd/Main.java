package com.diffblue.validatexsd;

import org.xml.sax.InputSource;
import org.xml.sax.SAXParseException;
import picocli.CommandLine;
import picocli.CommandLine.Command;
import picocli.CommandLine.Parameters;

import javax.xml.XMLConstants;
import javax.xml.transform.sax.SAXSource;
import javax.xml.validation.Schema;
import javax.xml.validation.SchemaFactory;
import javax.xml.validation.Validator;
import java.io.FileInputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.concurrent.Callable;

@Command(name = "validate-xsd", mixinStandardHelpOptions = true, version = "0.1",
  description = "tells you if given XML (read from stdin) matches a given XSD spec")
public class Main implements Callable<Integer> {
  @Parameters(index = "0")
  private Path xsdSchemaFilePath;

  @Override
  public Integer call() throws Exception {
    if(!Files.exists(xsdSchemaFilePath)) {
      System.err.printf("XSD schema file %s does not exist%n", xsdSchemaFilePath);
      return 1;
    }
    SchemaFactory factory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI);
    Schema schema = factory.newSchema(xsdSchemaFilePath.toFile());
    Validator validator = schema.newValidator();
    LoggingErrorHandler errorHandler = new LoggingErrorHandler();
    validator.setErrorHandler(errorHandler);
    SAXSource source = new SAXSource(new InputSource(System.in));
    try {
      validator.validate(source);
    } catch(SAXParseException e) {
      System.out.println(e.getMessage());
      return 1;
    }
    return errorHandler.hasErrorOccurred() ? 1 : 0;
  }

  public static void main(String[] args) {
    System.exit(new CommandLine(new Main()).execute(args));
  }
}
