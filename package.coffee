fs   = require 'fs'
find = require 'find'
find.file /\.agda$/, '.', (files) ->
  fs.writeFile 'package.json', JSON.stringify
    name: "agda-nplib"
    version: "0.0.1"
    description: "Extension of agda-stdlib"
    main: "agda-nplib.agda"
    scripts:
      test: "echo \"Error: no test specified\" && exit 1"
    files: [ "README" ].concat(files)
    repository:
      type: "git"
      url: "https://github.com/crypto-agda/agda-nplib"
    keywords: [
      "agda"
      "library"
    ]
    author: "Nicolas Pouillard"
    license: "BSD3"
    bugs:
      url: "https://github.com/crypto-agda/agda-nplib/issues"
    homepage: "https://github.com/crypto-agda/agda-nplib"
    dependencies:
      "agda-parametricity": ">= 0.0.3"
    agda:
      include: [
        "."
        "./lib"
      ]
