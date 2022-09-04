Hey there!

Right now this project is optimized to be easy for me (Blaine Hansen) to work in. This means it might not be easy for anyone to jump right in, and syntax or workflow may disregard certain community standards if I find them inconvenient. I'm not really concerned with the different standards of different language communities, and if I feel a language community has made a standard choice that makes code more difficult to work with, I will completely ignore it.

Although I will gladly accept pull requests that add conveniences for other setups, **I will deny any that disrupt my workflow**. I wish I had time to support other setups, but unfortunately working in Coq is very difficult and nit-picky, so the usual developer niceties such as using docker for local development aren't really practical.

Here are the main things I can think of:

- I run Ubuntu, so I have arranged all the scripts and build files to assume that. If you're interested in running on other systems, I'm afraid I have to leave you to your own devices. If a pull request makes a change that breaks the build on my system, I won't accept it. **I will gladly accept pull requests that make it possible to build everywhere!** However an important constraint is that [Coq interactive mode](https://packagecontrol.io/packages/Coq) must continue to work for me. If you can guide me toward a setup that allows other systems to run the build while working with Coq interactive mode, I'm happy to hear it.
- [I only ever use tabs over spaces for indentation, always.](https://adamtuttle.codes/blog/2021/tabs-vs-spaces-its-an-accessibility-issue/) I will only use spaces if some irreplaceable piece of the system will literally not work if I don't (`yml` is an example). I'm more likely to simply [not use](https://github.com/avh4/elm-format/issues/158) a language if it requires spaces. You can see this choice being made in all the `dune` files throughout the project. The OCaml ecosystem seems to think that a *single* space is easy enough to read, whereas I find it extremely difficult to read (which highlights the real reason tabs are better, everyone can configure their own tab display width).
- If some syntactic structure is "list-like" and supports one item per line, I will write it in a way that allows quickly adding and reordering lines without having to change the location of ending braces/parens. You can also see this in the `dune` files, where instead of using the lisp standard of placing closing parens on the same line as the last item, I place them on a new deindented line.

These probably seem trite and nit-picky, and maybe they are. I just don't want to fight with this code more than is necessary.

Thank you for your understanding!
