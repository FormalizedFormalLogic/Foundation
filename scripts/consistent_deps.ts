import projectManifest from "../lake-manifest.json" with { type: "json" };
import docbuildManifest from "../docbuild/lake-manifest.json" with {
  type: "json",
};

let flag = false;

const projectPackages = Object.fromEntries(
  projectManifest.packages.filter(({ rev }) => !!rev).map((
    { rev, name },
  ) => [name, rev]),
);
const docbuildPackages = Object.fromEntries(
  docbuildManifest.packages.filter(({ rev }) => !!rev).map((
    { rev, name },
  ) => [name, rev]),
);

const allPackages = { ...projectPackages, ...docbuildPackages };

for (const name in projectPackages) {
  if (projectPackages[name] !== allPackages[name]) {
    console.error(`Inconsistent dependency: ${name}`);
    flag = true;
  }
}

for (const name in docbuildPackages) {
  if (docbuildPackages[name] !== allPackages[name]) {
    console.error(`Inconsistent dependency: ${name}`);
    flag = true;
  }
}

if (flag) {
  console.error(
    "Some dependencies are inconsistent. Please run `lake update` to fix them.",
  );
  Deno.exit(1);
}

console.log("All dependencies are consistent.");
