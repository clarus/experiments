// @flow

export type t = {
  type: "Variable",
  name: string,
};

export function compile(expression: any): t {
  switch (expression.type) {
    case "Identifier":
      return {
        type: "Variable",
        name: expression.name,
      };
    default:
      throw new Error(JSON.stringify(expression, null, 2));
  }
}

export function print(expression: t): any {
  switch (expression.type) {
    case "Variable":
      return expression.name;
    default:
      return;
  }
}
