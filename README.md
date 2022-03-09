# TinyML

TinyML is a project assigned during Functional Language course at University of Padua.
The original source of the project is at the following link <https://github.com/alvisespano/FL-unipd-2021-22>. 
TinyML is a compiler, mainly a type checker for a tiny subset of the language ML.

## Implementation

The teacher provided a skeleton of the project: 

 - parser
 - type checker
 - evaluator.
 
 Students were asked to implement the type inference algorithm and all of its subfunction:
 
  - substitution
  - composition of substitution
  - unification
  - finally the inference itself.

## How to run

The teacher configured 4 different ways to run the project

 - Debug Interactive
 - Debug
 - Release
 - Release Interactive.

The project can be run via `dotnet run -c 'option'` (from `./TinyML` folder), option must be changed with any of the items listed above.
In order to run unit tests it is sufficient to run `dotnet test` from root folder.
