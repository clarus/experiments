const context = document.querySelector("body");
const instance = new Mark(context);
instance.markRegExp(/(^|[^a-z])(ether(eum)?)/iu, {
  accuracy: "exactly",
  className: "flip-text",
  element: "span",
  ignoreGroups: 1
});
document.querySelectorAll('.flip-text[data-markjs=true]').forEach(element => {
  element.style = 'display: inline-block; transform: scaleY(-1);';
});
