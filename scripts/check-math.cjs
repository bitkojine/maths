const { execFileSync } = require("node:child_process");
const { readFileSync } = require("node:fs");
const { mathjax } = require("mathjax-full/js/mathjax.js");
const { TeX } = require("mathjax-full/js/input/tex.js");
const { SVG } = require("mathjax-full/js/output/svg.js");
const { liteAdaptor } = require("mathjax-full/js/adaptors/liteAdaptor.js");
const { RegisterHTMLHandler } = require("mathjax-full/js/handlers/html.js");

RegisterHTMLHandler(liteAdaptor());
const document = mathjax.document("", {
  InputJax: new TeX({
    formatError(_jax, error) {
      throw error;
    },
  }),
  OutputJax: new SVG({ fontCache: "none" }),
});

const tracked = execFileSync("git", ["ls-files", "-z"], { encoding: "utf8" });
const files = process.argv.length > 2
  ? process.argv.slice(2)
  : tracked.split("\0").filter((path) => path.endsWith(".md"));

let checked = 0;
let failed = false;

function report(path, line, message) {
  console.error([path, line, message].join(": "));
  failed = true;
}

function checkFormula(path, line, formula, display) {
  try {
    if (/[<>]|&(?:lt|gt|amp|#\d+|#x[\da-f]+);/i.test(formula)) {
      throw new Error("Use \\lt and \\gt for inequalities in GitHub math.");
    }
    document.convert(formula, { display });
    checked++;
  } catch (error) {
    report(path, line, error.message);
  }
}

for (const path of files) {
  let fence;
  let formula = [];
  let start = 0;
  for (const [index, line] of readFileSync(path, "utf8").split(/\r?\n/).entries()) {
    if (fence) {
      const closing = line.trim();
      if (closing.startsWith(fence.marker) && /^(\x60+|~+)$/.test(closing)) {
        if (fence.math) checkFormula(path, start, formula.join("\n"), true);
        fence = undefined;
        formula = [];
      } else if (fence.math) {
        formula.push(line);
      }
      continue;
    }

    const opening = line.match(/^\s*(\x60{3,}|~{3,})\s*(\S*)/);
    if (opening) {
      fence = { marker: opening[1], math: opening[2] === "math" };
      start = index + 1;
      continue;
    }

    const prose = line.replace(/(\x60+).*?\1/g, "");
    if (/(?<!\\)\$\$/.test(prose)) {
      report(path, index + 1, "Use a fenced math block for display equations.");
      continue;
    }
    for (const match of prose.matchAll(/(?<!\\)\$((?:\\.|[^$\\])+)\$/g)) {
      checkFormula(path, index + 1, match[1], false);
    }
  }
  if (fence?.math) report(path, start, "Unclosed math fence.");
}

console.log("Rendered " + checked + " formulas in " + files.length + " Markdown files.");
process.exitCode = failed ? 1 : 0;
