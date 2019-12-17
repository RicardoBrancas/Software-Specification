# Second Project

This folder contains the solution for the second project
of the Software Specfication course, fall semestre 19/20.

## Reverse utility
This utility takes a non-empty file as input and a path
to a non existing file. It creates a new file at that
path containing the result of reversing the lines of the
original file.

## Grep utility
This utility is a simplified version of the grep command.
It returns YES when a match is found and NO otherwise.
Furthermore, if a match is found it returns the position.

It has two implementations:
- A naïve implentation wich runs in O(n^2) time
- And one based on the Knuth-Morris-Pratt algorithm which
  runs in O(n+m) time.

Ricardo Brancas 83557
