package it.unive.jlisa.program.cfg;

import it.unive.lisa.program.annotations.Annotations;
import it.unive.lisa.program.cfg.CodeLocation;
import it.unive.lisa.program.cfg.Parameter;
import it.unive.lisa.program.cfg.statement.Expression;
import it.unive.lisa.type.Type;

public class JavaParameter extends Parameter {

	private boolean isVarargs;

	public JavaParameter(CodeLocation location, String name, Type staticType, Expression defaultValue,
			Annotations annotations, boolean isVarargs) {
		super(location, name, staticType, defaultValue, annotations);
		this.isVarargs = isVarargs;
	}

	public boolean getIsVarargs() {
		return isVarargs;
	}



}


