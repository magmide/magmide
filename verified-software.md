---
title: "Verified Software"
---

# Preamble

Software is an increasingly critical component of our society, underpinning almost everything we do. It's also extremely vulnerable and unreliable. There are many areas where software *could* make society more efficient, transparent, and democratic, but because it is so insecure and fragile many are understandably resistant to rely on it for essential functions.

# Description

Using the same theoretical methods that underpin logic and mathematics, the field of formal verification seeks to find ways to prove that software has arbitrary logical qualities. Since software is complex and proving logical theorems can be difficult, the field has been mostly confined to academics verifying a few types of software. However recent advancements in the field promise to make it easier to verify software in its full complexity.

I've started work on a programming language called `Rok` that intends to combine recent advancements in formal verification with the existing state-of-the-art in programming language design, and I hope we can use it to improve our software infrastructure enough to feel confident relying on it in our democratic processes.

When the project has matured, I hope it will allow us to:

- Write software that is provably secure, making expensive hacks or privacy breaches a historical oddity. In our world, hackers search for new *vectors* of attack that utilize known vulnerabilities or attack types. In a world of verified software a hacker would have to invent an entirely new *type* of attack that was still present despite the fact that the target software has been proven to do precisely what it was specified to do and nothing else. This would raise the difficulty to perform any hack from a small amount of online research and computer savvy to years of dedicated expert research.
- Write software that is provably correct, making software much more reliable. Not all software requires perfect correctness, but there is a lot of foundational infrastructural software that everything else relies on and should absolutely be fully verified. Right now we live in a world where *no* software even has the *potential* to be fully verified.
- Make software more useful. When software is easier to make reliable and correct, it can become much more ambitious.

The project is obviously deeply technical, but if you are curious to learn more you can [visit the project's source code repository](TODO) or its [documentation site](TODO).

# Benefits

I believe all these goals are absolutely possible, and will just require a lot of hard work.

Software is basically the only thing in our world that could actually be provably correct. A computer program isn't really a physical object, it's just *information*, but it can still encode physical actions to take place in the real world. A computer program is a *logical machine*, so in the same way that it's possible to prove that `2 + 2 = 4`, we can prove that a computer program won't accidentally reveal passwords, or allow unauthorized access, or allow malicious programs to be executed, or *any other logical quality* we wish it to have.

# Potential Objections

Provably secure software doesn't solve all problems. Software often acts through physical objects such as motors or lights, and those are fallible in the same way all physical objects are. Also in many situations we still rely on potentially fallible human beings to act correctly on information given to them by computer programs.

# Open Questions

I actually feel there is very little unknown ahead of this project, at least from a technical perspective. Persistence and experimentation can guide us to the best way to build this language and encourage its widespread adoption.
