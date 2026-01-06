This is a repository with 3 main projects:

1. The lean-experiment.vercel.app website
2. A tauri/desktop version of that website
3. A VSCode extension, containing just the Mathlib Treemap visualizer.

Whenever you want to know something, and that thing can be learned easily by you, you should just run that command.
For example, if you want to know what's in a log file, just run `tail` on that file.
Or, if you want to know if something builds, just run a build command.
Avoid adding more than 5 flags when building a CLI tool. Instead, have the tool take in a configuration file
that way how to run the tool can be saved, put into version control, etc.