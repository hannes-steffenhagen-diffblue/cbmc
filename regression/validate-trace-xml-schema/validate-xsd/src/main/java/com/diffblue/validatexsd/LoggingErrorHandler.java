package com.diffblue.validatexsd;

import org.xml.sax.ErrorHandler;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

public class LoggingErrorHandler implements ErrorHandler {
  private boolean errorOccurred = false;

  @Override
  public void warning(SAXParseException e) throws SAXException {
    System.out.println("warning: " + e.getMessage());
  }

  @Override
  public void error(SAXParseException e) throws SAXException {
    System.out.println("error: " + e.getMessage());
    errorOccurred = true;
  }

  @Override
  public void fatalError(SAXParseException e) throws SAXException {
    System.out.println("fatal error: " + e.getMessage());
    errorOccurred = true;
  }

  public boolean hasErrorOccurred() {
    return errorOccurred;
  }
}
