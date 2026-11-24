# CombinatorialIdentities and Rencontres Numbers

For this project for 21-321, the main result is about formalizing identities 
about Rencontres numbers. The main identity is about counting permutations of 
n elements given k fixed points of the list. We formalize that this equals
n choose k multiplied by the number of derangements of the remaining n - k
elements.

## Files

1. 'CombinatorialIdentities/Basic.lean' contains the first few binomial 
  identities explored before diving into Mathlib and visualizing the right
  scope for this project (checkpoint 1 & 2)
2. 'CombinatorialIdentities/AMC.lean' contains AMC level problems and the 
  formalization of one of the questions (AMC10B #12). The skeleton for 
  AMC10A #10 was sketched out, but after consulting with the TAs, decided to 
  move towards a more general identity with more rigor, hence the AMC10A being
  unfinished. (checkpoint 2 & 3)
3. 'CombinatorialIdentities/Rencontres.lean' is the main file containig the 
  formalization of the rencontres identity mentioned above. The supporting
  theorems and lemmas are included with some definitions to build the 
  foundation. (checkpoint 3, 4 & 5)


## 2. Get the Mathlib cache

Compiling Mathlib from source takes hours, so download the prebuilt files instead:

```bash
lake exe cache get
```

Re-run this whenever you change the Mathlib version (or if your editor starts rebuilding
Mathlib files).

## 3. Build and work on the project

```bash
lake build
```

- Put your Lean files under `MyProject/` and import each one from `MyProject.lean`, so that
  `lake build` (and CI) checks them.
- Open the repository folder (not a single file) in VS Code with the Lean 4 extension.

## Updating Mathlib

Change the `rev` under `[[require]]` in `lakefile.toml` to the new Mathlib tag, and set
`lean-toolchain` to match. Then run:

```bash
lake update mathlib
lake exe cache get
lake build
```

Alternatively, run the **Update Dependencies** workflow from the GitHub *Actions* tab: it
opens a pull request if the update builds, or an issue if it doesn't. (Uncomment the
`schedule` block in `.github/workflows/update.yml` to run it automatically.)

## GitHub setup

- **CI**: every push and pull request is built by `.github/workflows/lean_action_ci.yml`.
- To let the update workflow open pull requests, go to **Settings → Actions → General** and
  tick **Allow GitHub Actions to create and approve pull requests**.
- To publish docs to GitHub Pages, set **Settings → Pages → Source** to "GitHub Actions" and
  uncomment the `docgen-action` line in `lean_action_ci.yml`.
