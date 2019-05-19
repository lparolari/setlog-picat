# setlog-picat-draft

The objective of this repository is to track changes of drafts and proof of concepts for the [{log}](http://people.dmi.unipr.it/gianfranco.rossi/setlog.Home.html) (read setlog)
language implementation in picat.

The work in this repository is strongly referenced to the {log} project.


## Install
- First, you need to install [picat](http://picat-lang.org/).
```
# for Windows
curl -O http://picat-lang.org/download/picat25_win64.zip 
# for Linux
curl -O http://picat-lang.org/download/picat25_linux64.tar.gz
# for MacOs
curl -O http://picat-lang.org/download/picat25_macx.tar.gz
``` 
for other versions or for source code, visit the [homepage](http://picat-lang.org/).
**Note**: the version listed here might not be the latest. Check the website.

- Unzip it in some folder of your computer.

- Add the picat folder to the environment variable `PATH`
```
# in Linux
export PATH="$PATH:/path/to/picat"
```


## Usage

Download the repository
```
git clone https://github.com/lparolari/setlog-picat-draft.git
cd setlog-picat-draft
```

Execute the picat code
```
$ picat test1.pi
```
or, in picat interpreter
```
$ picat
$ Picat> cl(test1).
$ Picat> main.
```


## Author
Luca Parolari <<luca.parolari23@gmail.com>>


## License
```
Copyright (c) 2019 Luca Parolari

Permission is hereby granted, free of charge, to any person
obtaining a copy of this software and associated documentation
files (the "Software"), to deal in the Software without
restriction, including without limitation the rights to use,
copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following
conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.
```
