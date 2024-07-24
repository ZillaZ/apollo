# The Apollo programming language
Still in early development.
### This is just a personal project! Do not expect anything at production level

Apollo uses the GCC backend to generate bytecode. You need to have libgccjit on your machine to use the language.

### Today, Apollo supports:
- [Primitive Types](#primitives)
- [Variables](#variables)
- [Structs](#structs)
- [Arrays](#arrays)
- [Functions](https://github.com/ZillaZ/apollo/blob/main/examples/functions/main.apo)
- [Traits](https://github.com/ZillaZ/apollo/blob/main/examples/traits/main.apo)
- [Namespaces](https://github.com/ZillaZ/apollo/tree/main/examples/namespaces)

### Primitives
```
i1 i2 i4 i8
f4
string
char
bool
```

### Variables
```
let name = "Lucas"
```

### Structs
```
struct Person {
  name: string
  age: i4
}
```

### Arrays
```
let array = array(i4)[1 2 3]
```

# Todo
- Add dynamic libraries support
- Comptime memory management
- Parallel computing support (Threads and Forks)
- Sugar syntax for type casting
- Improve operations parsing
- Refactor the entire codebase (it is pretty ugly...)
