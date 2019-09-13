// @flow
import React, {PureComponent} from "react";
import codeFrame from "babel-code-frame";
import {parse} from "@babel/parser";
import doc from "prettier/doc.js";
import * as Program from "./compiler/program.js";
import Output from "./Output.js";
import "./App.css";

type Props = {};

type State = {
  jsInput: string,
};

export default class App extends PureComponent<Props, State> {
  state: State = {
    jsInput:
      `// Some examples

const b = false;

function id<A, B>(x: A): A {
  return x;
}

function basicTypes(n: number, m: number): string {
  return "OK";
}
`,
  };

  onChangeJsInput = (event: SyntheticEvent<*>) => {
    this.setState({jsInput: event.currentTarget.value});
  };

  getJsAst(jsInput: string): any | string {
    try {
      const ast = parse(jsInput, {
        plugins: [
          'flow',
          'jsx',
        ],
        sourceType: 'module',
      });

      return ast;
    } catch (error) {
      const {loc} = error;

      if (loc) {
        return `${error.message}\n\n${codeFrame(jsInput, loc.line, loc.column)}`;
      }

      throw error;
    }
  }

  getCoqAst(jsAst: any): any {
    try {
      return Program.compile(jsAst.program);
    } catch (error) {
      return `Error:\n${error.message}`;
    }
  }

  getCoqString(coqAst: Program.t): string {
    return doc.printer.printDocToString(Program.print(coqAst), {printWidth: 40, tabWidth: 2}).formatted;
  }

  render() {
    const {jsInput} = this.state;
    const jsAst = this.getJsAst(jsInput);
    const coqAst = typeof jsAst !== "string" ? this.getCoqAst(jsAst) : "";
    const coqString = typeof coqAst !== "string" ? this.getCoqString(coqAst) : "";

    return (
      <div>
        <div className="split js-source">
          <textarea onChange={this.onChangeJsInput} value={jsInput} />
        </div>
        <div className="split js-ast">
          <Output output={jsAst} />
        </div>
        <div className="split coq-ast">
          <Output output={coqAst} />
        </div>
        <div className="split coq-source">
          <Output output={coqString} />
        </div>
      </div>
    );
  }
}
