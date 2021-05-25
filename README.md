# setlog-picat 

[![forthebadge](https://forthebadge.com/images/badges/built-with-love.svg)](https://forthebadge.com) [![forthebadge](https://forthebadge.com/images/badges/contains-cat-gifs.svg)](https://forthebadge.com)

[![PRs Welcome](https://img.shields.io/badge/PRs-welcome-brightgreen.svg?style=flat-square)](http://makeapullrequest.com) [![GitHub issues](https://img.shields.io/github/issues-raw/lparolari/setlog-picat.svg)](https://github.com/lparolari/setlog-picat/issues) [![PRs Welcome](https://img.shields.io/github/license/lparolari/setlog-picat.svg)](http://makeapullrequest.com)

[here goes a gif explaining what this repository is about]

**:warning: This repository contains the code for my bachelor degree thesis project :relaxed:**

*setlog-picat* is a pure implementation of [{log}](http://people.dmi.unipr.it/gianfranco.rossi/setlog.Home.html) (read
setlog) in [picat](http://picat-lang.org/). This work is related to the {log} project.

{log} project aims at the design and development of a Constraint Logic Programming language that embodies the
fundamental forms of set designation and a number of primitive operations for set management. 


## Table of Contents

   * [<g-emoji class="g-emoji" alias="floppy_disk" fallback-src="https://github.githubassets.com/images/icons/emoji/unicode/1f4be.png">💾</g-emoji> Install](#-install)
      * [Usage](#usage)
   * [<g-emoji class="g-emoji" alias="gift" fallback-src="https://github.githubassets.com/images/icons/emoji/unicode/1f381.png">🎁</g-emoji> Contributing](#-contributing)
   * [<g-emoji class="g-emoji" alias="heart" fallback-src="https://github.githubassets.com/images/icons/emoji/unicode/2764.png">❤️</g-emoji> Authors](#️-authors)
   * [<g-emoji class="g-emoji" alias="mortar_board" fallback-src="https://github.githubassets.com/images/icons/emoji/unicode/1f393.png">🎓</g-emoji> License](#-license)


## :rocket: Getting Started

{log} is a language for binary relations over sets. 

Below you will find everything you need to know about this setlog implementation. Start form the [install](#-install) 
section if you want to play with the setlog solver, type in some formulas and see the magic.

## :floppy_disk: Install

- Install the Picat engine following the install procedure [here](http://picat-lang.org/).
- Download the setlog engine for picat
```
git clone https://github.com/lparolari/setlog-picat-draft.git
cd setlog-picat-draft
```

## :arrow_forward: Usage

```
$ picat               # start picat interpreter.
$ Picat> cl(setlog).  # compile and load the setlog module into picat
$ Picat> setlog.      # start setlog intepreter.
$ {log} => Enter your formula here...
```



## :gift: Contributing

1. Fork it!
2. Create your feature branch: `git checkout -b my-new-feature`
3. Commit your changes: `git commit -am 'Add some feature'`
4. Push to the branch: `git push origin my-new-feature`
5. Submit a pull request :D


## :heart: Authors

Luca Parolari <<luca.parolari23@gmail.com>>


## :mortar_board: License

This project is licensed under MIT license. See [LICENSE.txt](LICENSE.txt) file for details.
