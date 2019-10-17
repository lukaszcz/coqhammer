This file contains a few simple general rules for keeping code clean,
which are not difficult to apply and save a lot of effort
later. Please, read all points and try to follow.

1. Do *not* use TABs, under any circumstances. Set your editor to
   automatically convert them to spaces.

2. Make sensible indentation. Do *not* use TABs.

3. Within reason, try to follow the coding style of the code already
   present in the repository, i.e., the same kind of indentation
   (number of spaces), the same way of inserting newlines, etc.

4. As a general rule, avoid copy & paste. Instead, abstract out a more
   general parameterised function.

5. Try to make commits which include only things directly relevant to
   what you're changing. Do not make changes which do nothing (don't
   change the behaviour of the code), unless your commit is explicitly
   about refactoring (cleaning up) code. Avoid including outcommented
   code, changes of parameters you just used for debugging, hardcoded
   paths, etc.

   **Hint**: use `git diff` to review your changes before committing.

6. Try to split commits that do many unrelated things into several
   commits, each doing one thing. Splitting commits might not always
   be worth the effort, but it's always worth trying to do this and to
   keep it in mind. Then the diffs are easy to read, and you can
   easily find what was changed when and for what purpose.

7. Remove unused code, don't comment it out. With git you can always
   go back, and really removing things shows up on diffs.

8. When starting on a new thing make a branch (`git branch`, `git
   checkout -b`) from the most recent development version for a stable
   version of Coq. This will be in one of the coq8.X branches (ask if
   not sure). This is *never* the master branch. Branching out from
   master is bad because the master branch is synchronised with the
   most recent unstable development version of Coq, which constantly
   changes and you're then suddenly no longer able to compile things
   you wrote a few days/weeks/months ago.
