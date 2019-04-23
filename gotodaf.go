package main

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"io/ioutil"
	"os"
	"regexp"
	"strings"

	"golang.org/x/tools/go/ast/astutil"
)

var endpointPrefix = "tmp_ep"
var endpointCounter = 0

func loadFileIntoArray(filename string) (lines []string) {
	b, e := ioutil.ReadFile(filename)
	if e != nil {
		panic(e)
	}
	array := bytes.Split(b, []byte("\n"))
	ret := make([]string, len(array))

	for index, line := range array {
		ret[index] = fmt.Sprintf("%s\n", line)
	}
	return ret
}

func printFileArray(lines []string) {
	for _, line := range lines {
		fmt.Print(line)
	}
}

func grabIndentation(statement string) string {
	regex, err := regexp.Compile("(\\s*)")
	if err != nil {
		fmt.Println("Error:", err)
		return ""
	}
	return regex.FindString(statement)

}

func applyFunction(c *astutil.Cursor) bool {
	if ret, ok := c.Node().(*ast.ForStmt); ok {
		init := ret.Init
		if init != nil {
			c.InsertBefore(init)
		}
		ret.Init = nil
		post := ret.Post
		if post != nil {
			ret.Body.List = append(ret.Body.List, post)
			ret.Post = nil
		}
	}

	return true
}

var fset = token.NewFileSet() // positions are relative to fset

func main() {
	if len(os.Args) <= 1 {
		fmt.Println("Build the tool with go build gotodaf.go, Usage: ./gotodaf <input-file>")
		return
	}
	if strings.Contains(os.Args[1], "-h") {
		fmt.Println("Build the tool with go build gotodaf.go, Usage: ./gotodaf <input-file>")
		return
	}
	filepath := os.Args[1]
	outfile := "out.dfy"
	regex, err := regexp.Compile("/?(\\w*).go")
	filename := regex.FindStringSubmatch(filepath)[1]
	if len(filepath) <= 0 {
		fmt.Println("Error: filepath not given")
		return
	}

	f, err := parser.ParseFile(fset, filepath, nil, parser.ParseComments)
	if err != nil {
		fmt.Println(err)
		return
	}
	file, err := os.Create(outfile)
	if err != nil {
		fmt.Println(err)
	}
	//delete the file we created when the program exits
	defer os.Remove(outfile)
	//TODO: command line option for warnings
	//TODO: when moving brackets, print out a notice of what line you're moving it from and to
	//especially if there isn't one to be moved above it
	//TODO: clean up code and turn into a switch
	//TODO: add command line option for output file
	//TODO: new syntax for writing channel descriptions - S5
	//ast.Print(fset, f)
	newN := astutil.Apply(f, nil, applyFunction)

	//Converts the AST back to code and writes it out to a file
	printer.Fprint(file, fset, newN)
	//Load that file into an array and then parse its AST
	//the fprint call takes a file object
	//whereas the function loadFileIntoArray takes the string name of the file
	fileSlice := loadFileIntoArray(outfile)
	f, err = parser.ParseFile(fset, outfile, nil, parser.ParseComments)
	ast.Inspect(f, func(n ast.Node) bool {
		if ret, ok := n.(*ast.UnaryExpr); ok {
			if ret.Op == token.ARROW {
				//we have a receive I believe
				ch, ok := ret.X.(*ast.Ident)
				if ok {
					line := fileSlice[fset.Position(ret.Pos()).Line-1]
					receiveStr := fmt.Sprintf("%s.receive()", ch.Name)
					toReplace := fmt.Sprintf("<-%s", ch.Name)
					line = strings.Replace(line, toReplace, receiveStr, -1)
					fileSlice[fset.Position(ret.Pos()).Line-1] = line
				}

			}
		}
		//Remove imports
		if ret, ok := n.(*ast.GenDecl); ok && ret.Tok == token.IMPORT {
			//loop through all import lines and remove them
			if fset.Position(ret.Rparen).Line <= 0 {
				fileSlice[fset.Position(ret.Pos()).Line-1] = ""
				return true
			}
			for i := fset.Position(ret.Pos()).Line - 1; i != fset.Position(ret.Rparen).Line; i++ {
				fileSlice[i] = ""
			}
		}
		//Remove package declaration
		if ret, ok := n.(*ast.File); ok {
			fileSlice[fset.Position(ret.Package).Line-1] = ""
		}
		//Go func() call
		if ret, ok := n.(*ast.GoStmt); ok {
			line := fileSlice[fset.Position(ret.Pos()).Line-1]
			indent := grabIndentation(line)
			regex, err := regexp.Compile("go (.*)")
			if err != nil {
				fmt.Printf("%v is the error\n", err)
			}
			val := regex.FindStringSubmatch(line)
			fileSlice[fset.Position(ret.Pos()).Line-1] = indent + val[1] + "\n"
		}
		if ret, ok := n.(*ast.FuncDecl); ok {
			//Function declarations
			line := fileSlice[fset.Position(ret.Pos()).Line-1]
			fileSlice[fset.Position(ret.Pos()).Line-1] = strings.Replace(line, "func ", "method ", 1)
			params := ret.Type.Params.List
			convertedParams := ""
			//convert params
			for index := range params {
				varName := params[index].Names[0].Name
				varType := ""
				if arrType, ok := params[index].Type.(*ast.ArrayType); ok {
					varType = "array<" + arrType.Elt.(*ast.Ident).Name + ">"
				} else if channelType, ok := params[index].Type.(*ast.ChanType); ok {
					msgType := channelType.Value.(*ast.Ident)
					varType = "Endpoint<" + msgType.Name + ">"
				} else if retType, ok := params[index].Type.(*ast.Ident); ok {
					varType = retType.Name
				}
				convertedParams += varName + ": " + varType
				if index < len(params)-1 {
					convertedParams += ", "
				}

			}
			convertedParams += ")"
			//parse returns
			returnsStr := ""
			if ret.Type.Results != nil {
				returns := ret.Type.Results.List
				returnsStr = "returns ("
				for retIndex := range returns {
					retName := ""
					if len(returns[retIndex].Names) > 0 {
						retName = returns[retIndex].Names[0].Name
					}
					varType := ""
					//arrays
					//channels
					//others
					if retType, ok := returns[retIndex].Type.(*ast.ArrayType); ok {
						varType = "array<" + retType.Elt.(*ast.Ident).Name + ">"
					} else if _, ok := returns[retIndex].Type.(*ast.ChanType); ok {
						varType = "Endpoint"
					} else if retType, ok := returns[retIndex].Type.(*ast.Ident); ok {
						varType = retType.Name
					}
					returnsStr += retName + ":" + varType
					if retIndex != len(returns)-1 {
						returnsStr += ", "
					} else {
						returnsStr += ")"
					}

				}
			}
			regex, _ := regexp.Compile("method \\w*\\(")
			val := regex.FindString(fileSlice[fset.Position(ret.Pos()).Line-1])
			paramStr := fmt.Sprintf("%v%v%v{\n", val, convertedParams, returnsStr)
			fileSlice[fset.Position(ret.Pos()).Line-1] = paramStr

		}
		if ret, ok := n.(*ast.CallExpr); ok {
			if function, ok := ret.Fun.(*ast.Ident); ok {
				if function.Name == "close" {
					line := fileSlice[fset.Position(ret.Pos()).Line-1]
					indent := grabIndentation(line)
					regex, _ := regexp.Compile("close\\((.*)\\)")
					val := regex.FindStringSubmatch(line)
					closeStr := fmt.Sprintf(indent+"%v.close()\n", val[1])
					fileSlice[fset.Position(ret.Pos()).Line-1] = closeStr
				}
				if function.Name == "len" {
					line := fileSlice[fset.Position(ret.Pos()).Line-1]
					regex, _ := regexp.Compile("len\\((.*)\\)")
					val := regex.FindStringSubmatch(line)
					lenStr := fmt.Sprintf("%v.Length", val[1])
					line = strings.Replace(line, "len("+val[1]+")", lenStr, 1)
					fileSlice[fset.Position(ret.Pos()).Line-1] = line
				}
			}
		}
		if ret, ok := n.(*ast.ForStmt); ok {
			line := fileSlice[fset.Position(ret.Pos()).Line-1]
			line = strings.Replace(line, "for", "while", -1)
			fileSlice[fset.Position(ret.Pos()).Line-1] = line
		}
		if ret, ok := n.(*ast.AssignStmt); ok {
			//calling a function
			//Change Channel Creation
			if call, ok := ret.Rhs[0].(*ast.CallExpr); ok {
				if function, ok := call.Fun.(*ast.Ident); ok {
					if function.Name == "make" {
						if typeOf, ok := ret.Rhs[0].(*ast.CallExpr).Args[0].(*ast.ChanType); ok {
							//making a channel
							//want to change it from ch := make(chan int)
							//to ch := new Channel.Channel("pattern")
							if ident, ok := ret.Lhs[0].(*ast.Ident); ok {
								line := fileSlice[fset.Position(ret.Pos()).Line-1]
								indent := grabIndentation(line)
								regex, _ := regexp.Compile("\\/\\*\\?(.*)\\?\\*\\/")
								val := regex.FindStringSubmatch(line)
								if len(val) == 0 {
									fmt.Println("Error: There is no pattern for this channel")
									return true
								}
								if chanType, ok := typeOf.Value.(*ast.Ident); ok {
									createStr := fmt.Sprintf(indent+"%s := new BinaryChannel<%v>(%s)\n",
										ident.Name, chanType.Name, val[1])
									fileSlice[fset.Position(ret.Pos()).Line-1] = createStr
								}

							}
						}
					}
				}
			}

			//variable assignment
			if ident, ok := ret.Lhs[0].(*ast.Ident); ok {
				line := fileSlice[fset.Position(ret.Pos()).Line-1]
				varName := ident.Name

				//new variable - needs var beforehand
				if ret.Tok == token.DEFINE {
					line = strings.Replace(line, varName, "var "+varName, 1)
				}
				line = strings.Replace(line, " =", " :=", 1)
				fileSlice[fset.Position(ret.Pos()).Line-1] = line
			}
			//array assignment
			if indexExpr, ok := ret.Lhs[0].(*ast.IndexExpr); ok {
				line := fileSlice[fset.Position(ret.Pos()).Line-1]
				varName := indexExpr.X.(*ast.Ident).Name

				//new variable - needs var beforehand
				if ret.Tok == token.DEFINE {
					line = strings.Replace(line, varName, "var "+varName, 1)
				}
				line = strings.Replace(line, " =", " :=", 1)
				fileSlice[fset.Position(ret.Pos()).Line-1] = line
			}
			//arrays
			if ret, ok := ret.Rhs[0].(*ast.CompositeLit); ok {
				line := fileSlice[fset.Position(ret.Pos()).Line-1]
				if arrType, ok := ret.Type.(*ast.ArrayType).Elt.(*ast.Ident); ok {
					line = strings.Replace(line, "[]"+arrType.Name, "", -1)
					line = strings.Replace(line, "{", "[", -1)
					line = strings.Replace(line, "}", "]", -1)
					fileSlice[fset.Position(ret.Pos()).Line-1] = line
				}
			}

		} else {
			//Send Statements
			ret, ok := n.(*ast.SendStmt)
			if ok {
				ch := ret.Chan.(*ast.Ident)
				line := fileSlice[fset.Position(ret.Pos()).Line-1]
				indent := grabIndentation(line)
				regex, err := regexp.Compile("(<-)\\s(.*)")
				if err != nil {
					fmt.Printf("%v is the error\n", err)
				}
				val := regex.FindStringSubmatch(line)
				sendStr := fmt.Sprintf(indent+"%s.send(%v)\n", ch.Name, val[2])
				fileSlice[fset.Position(ret.Pos()).Line-1] = sendStr
			}
		}
		//Print Statements
		if ret, ok := n.(*ast.Ident); ok {
			if ret.Name == "fmt" {
				regex, _ := regexp.Compile("\\((.*)\\)")
				line := fileSlice[fset.Position(ret.Pos()).Line-1]
				indent := grabIndentation(line)
				val := regex.FindString(line)
				printStr := fmt.Sprintf(indent+"print%v\n", val)
				fileSlice[fset.Position(ret.Pos()).Line-1] = printStr
			}
		}
		return true
	})
	ast.Inspect(f, func(n ast.Node) bool {
		//skip block statements, if statements and for statements
		_, isIf := n.(*ast.IfStmt)
		_, isFor := n.(*ast.ForStmt)
		if _, isBlock := n.(*ast.BlockStmt); !(isIf || isBlock || isFor) {
			if ret, ok := n.(ast.Stmt); ok {

				line := fileSlice[fset.Position(ret.Pos()).Line-1]
				fileSlice[fset.Position(ret.Pos()).Line-1] = strings.Replace(line, "\n", ";\n", -1)
			}
		}
		return true
	})
	fileSlice = addHeader(fileSlice, filename)
	fileSlice = parseComments(fileSlice)
	printFileArray(fileSlice)

}

func parseComments(file []string) []string {
	for index := 0; index < len(file); index++ {
		if strings.Contains(file[index], "/*?") {
			file[index] = strings.Replace(file[index], "/*?", "", -1)
		}
		if strings.Contains(file[index], "?*/") {
			file[index] = strings.Replace(file[index], "?*/", "", -1)
		}
		if strings.Contains(file[index], "//?") {
			file[index] = strings.Replace(file[index], "//?", "", -1)
		}
		if strings.Contains(file[index], "/*^") {
			i := index - 1
			//loop backwards in the file until you find a matching opening brace to remove
			for ; !strings.Contains(file[i], "{") && i > 0; i-- {
			}
			file[i] = strings.Replace(file[i], "{", "", -1)
			file[index] = strings.Replace(file[index], "/*^", "", -1)
		}
		if strings.Contains(file[index], ">*/") {
			file[index] = strings.Replace(file[index], ">*/", "{", -1)
		}
		if strings.Contains(file[index], "/*+*/") || strings.Contains(file[index], "/*-*/") {
			//find all instances of endpoint annotations
			regex, _ := regexp.Compile("\\/\\*[\\+\\-]\\*\\/")
			matches := regex.FindAllStringSubmatch(file[index], -1)
			//need to create a new endpoint variable for each match
			for i := 0; i < len(matches); i++ {
				regex, _ = regexp.Compile("[ ,(]?(\\w*)\\s?\\/\\*[\\+\\-]\\*\\/")
				val := regex.FindStringSubmatch(file[index])
				positive := false
				//there is only ever one submatch
				if strings.Contains(matches[i][0], "+") {
					positive = true
				}
				indent := grabIndentation(file[index])
				endpointVar := fmt.Sprintf("%v%v", endpointPrefix, endpointCounter)
				endpointCounter++
				prevStr := ""
				insertStr := ""
				if positive {
					insertStr = fmt.Sprintf("%v.getPositiveEndpoint();", val[1])
					prevStr = fmt.Sprintf("%v /*+*/", val[1])
				} else {
					insertStr = fmt.Sprintf("%v.getNegativeEndpoint();", val[1])
					prevStr = fmt.Sprintf("%v /*-*/", val[1])
				}
				//create endpoint variable and insert into file
				newVar := indent + "var " + endpointVar + " := " + insertStr
				file = insertIntoFile(file, index, newVar)
				index++
				//edit function call to use endpoint variable
				file[index] = strings.Replace(file[index], prevStr, endpointVar, 1)
			}
		}

	}
	return file
}

func insertIntoFile(file []string, i int, str string) []string {
	//dummy value
	file = append(file, "")
	//copy(dst,src)
	copy(file[i+1:], file[i:])
	file[i] = str + "\n"
	return file
}

func addHeader(file []string, filename string) []string {
	moduleName := fmt.Sprintf("module %s{ \n", filename)
	file = insertIntoFile(file, 0, moduleName)
	file = insertIntoFile(file, len(file), "}")
	return file
}
