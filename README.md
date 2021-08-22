## Zac Programming Language
An interactive scripting language where you can read and modify code comments as if they were regular strings. Add and view text-based visualizations and debugging information inside your source code file.

![GoL](.README_assets/GoL.gif)

Since this is an interactive editor, the best examples are moving use cases.

#### Built-in Help
![help](.README_assets/help.gif)

#### Workbook style examples that don't go out of sync
![fib](.README_assets/fib.gif)

### Cargo Install Instructions
Make sure you have the [Cargo package manager](https://crates.io/) with a recent nightly Rust, and from inside this
directory:
```console 
cargo install --path .
```

### How To Run
As an example, open [examples/hello.zac](examples/hello.zac) in your editor.

### More examples
- [GoL.zac](examples/GoL.zac)
- [fib.zac](examples/fib.zac)
- [hello.zac](examples/fib.zac)

#### It's Better With Syntax Highlighting
If you're using Vim, there's a [syntax file](syntax_highlighting/) in the repo. Put this in your `~/.vim/syntax` directory, or `~/.config/nvim/syntax` if you're using Neovim, and follow the instructions at the top of the file.


### Status
This is a proof-of-concept developed in the first [Lang Jam](langjam/langjam), a 2-day competition to design a programming language around the theme `first-class comments`.

<img src=".README_assets/firstclass.png" height="100px">
Submitted to the contest under the name SOLDIER.
