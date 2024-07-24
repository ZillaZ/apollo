# The Apollo programming language
Still in early development.
### This is just a personal project! Do not expect anything at production level

Apollo uses the GCC backend to generate bytecode. You need to have libgccjit on your machine to use the language.

### Today, Apollo supports:
- [Primitive Types](#primitives)
- [Variables](#variables)
- [Structs](#structs)
- [Arrays](#arrays)
- [Functions](#functions)
- [Traits](#traits)

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

### Functions
```
fn new_person(name: string, age: i4) -> Person {
  return new Person {
    name: name
    age: age
  }
}
```

### Traits
```
trait Person {
  name: string
  age: i4
}

fn print_person(person: 'Person) {
  printf("%s is %d years old", person.name, person.age)
  return
}

struct Student {
  #[Person]
  class: string
}
```

# Todo
- Add dynamic libraries support
- Comptime memory management
- Parallel computing support (Threads and Forks)
- Sugar syntax for type casting
- Improve operations parsing
- Refactor the entire codebase (it is pretty ugly...)
