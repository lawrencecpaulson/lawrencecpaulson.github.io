---
layout: post
title: Proving a lower bound where the derivative is undefined at an endpoint
usemathjax: true 
tags: [examples, Isar, formalised mathematics]
---
The previous post concerned exact numerical calculations, culminating in an example of establishing a numerical lower bound for a simple mathematical formula, fully automatically.
Automation, above all else, is the key to the success of formal verification,
but a numerical approach is not always good enough. In that example,
We could get three significant digits quickly, four significant digits slowly
and the exact lower bound never.
As every calculus student knows, to locate a minimum or maximum, you take the derivative
and solve for the point at which it vanishes. 
The desired property can then be shown using the main value theorem.
