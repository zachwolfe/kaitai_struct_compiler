package io.kaitai.struct.languages

import io.kaitai.struct._
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.datatype._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.exprlang.Ast.expr
import io.kaitai.struct.format._
import io.kaitai.struct.languages.components._
import io.kaitai.struct.translators.{CSharpTranslator, TypeDetector}

class CSharpCompiler(typeProvider: ClassTypeProvider, config: RuntimeConfig)
  extends LanguageCompiler(typeProvider, config)
    with UpperCamelCaseClasses
    with ObjectOrientedLanguage
    with SingleOutputFile
    with AllocateIOLocalVar
    with EveryReadIsExpression
    with FetchInstances
    with EveryWriteIsExpression
    with GenericChecks
    with UniversalFooter
    with UniversalDoc
    with SwitchIfOps
    with NoNeedForFullClassPath {
  import CSharpCompiler._

  val translator = new CSharpTranslator(typeProvider, importList, config)

  /** See [[subIOWriteBackHeader]] => the code generated when `true` will be inside the definition
   * of the "writeBackHandler" callback function. */
  private var inSubIOWriteBackHandler = false;

  override def universalFooter: Unit = {
    out.dec
    out.puts("}")
  }

  override def indent: String = "    "
  override def outFileName(topClassName: String): String = s"${type2class(topClassName)}.cs"

  override def outImports(topClass: ClassSpec) =
    importList.toList.map((x) => s"using $x;").mkString("", "\n", "\n")

  override def fileHeader(topClassName: String): Unit = {
    outHeader.puts(s"// $headerComment")
    outHeader.puts

    var ns = "Kaitai"
    if (!config.dotNetNamespace.isEmpty)
      ns = config.dotNetNamespace

    if (ns != "Kaitai")
      importList.add("Kaitai")

    out.puts
    out.puts(s"namespace $ns")
    out.puts(s"{")
    out.inc
  }

  override def fileFooter(topClassName: String): Unit = universalFooter

  override def classHeader(name: String): Unit = {
    out.puts(s"public partial class ${type2class(name)} : $kstructNameFull")
    out.puts(s"{")
    out.inc

    // `FromFile` is generated only for parameterless types
    if (typeProvider.nowClass.params.isEmpty) {
      out.puts(s"public static ${type2class(name)} FromFile(string fileName)")
      out.puts(s"{")
      out.inc
      out.puts(s"return new ${type2class(name)}(new $kstreamName(fileName));")
      out.dec
      out.puts("}")
      out.puts
    }
  }

  override def classConstructorHeader(name: String, parentType: DataType, rootClassName: String, isHybrid: Boolean, params: List[ParamDefSpec]): Unit = {
    typeProvider.nowClass.meta.endian match {
      case Some(_: CalcEndian) | Some(InheritedEndian) =>
        out.puts(s"private bool? ${privateMemberName(EndianIdentifier)};")
      case _ =>
        // no _is_le variable
    }

    val addStreamDefault = if (config.readWrite) " = null" else ""
    val addEndian = if (isHybrid) ", bool? isLe = null" else ""

    val pIo = paramName(IoIdentifier)
    val pParent = paramName(ParentIdentifier)
    val pRoot = paramName(RootIdentifier)

    val paramsArg = Utils.join(params.map((p) =>
      s"${kaitaiType2NativeType(p.dataType)} ${paramName(p.id)}"
    ), "", ", ", ", ")

    out.puts(
      s"public ${type2class(name)}($paramsArg" +
        s"$kstreamName $pIo$addStreamDefault, " +
        s"${kaitaiType2NativeType(parentType)} $pParent = null, " +
        s"${type2class(rootClassName)} $pRoot = null$addEndian) : base($pIo)"
    )
    out.puts(s"{")
    out.inc
    handleAssignmentSimple(ParentIdentifier, pParent)

    handleAssignmentSimple(
      RootIdentifier,
      if (name == rootClassName) s"$pRoot ?? this" else pRoot
    )

    if (isHybrid)
      handleAssignmentSimple(EndianIdentifier, "isLe")

    // Store parameters passed to us
    params.foreach((p) => handleAssignmentSimple(p.id, paramName(p.id)))
  }

  override def runRead(name: List[String]): Unit =
    out.puts("_read();")

  override def runReadCalc(): Unit = {
    out.puts
    out.puts(s"if (${privateMemberName(EndianIdentifier)} == null) {")
    out.inc
    out.puts(s"throw new ${ksErrorName(UndecidedEndiannessError)}();")
    importList.add("System")
    out.dec
    out.puts(s"} else if (${privateMemberName(EndianIdentifier)} == true) {")
    out.inc
    out.puts("_readLE();")
    out.dec
    out.puts("} else {")
    out.inc
    out.puts("_readBE();")
    out.dec
    out.puts("}")
  }

  override def runWriteCalc(): Unit = {
    out.puts
    out.puts(s"if (${privateMemberName(EndianIdentifier)} == null) {")
    out.inc
    out.puts(s"throw new ${ksErrorName(UndecidedEndiannessError)}();")
    importList.add("System")
    out.dec
    out.puts(s"} else if (${privateMemberName(EndianIdentifier)} == true) {")
    out.inc
    out.puts("_write_SeqLE();")
    out.dec
    out.puts("} else {")
    out.inc
    out.puts("_write_SeqBE();")
    out.dec
    out.puts("}")
  }

  override def readHeader(endian: Option[FixedEndian], isEmpty: Boolean) = {
    endian match {
      case Some(e) =>
        out.puts(s"private void _read${Utils.upperUnderscoreCase(e.toSuffix)}()")
      case None =>
        out.puts(s"${if (!config.autoRead) "public override" else "private"} void _read()")
    }
    out.puts("{")
    out.inc
  }

  override def fetchInstancesHeader(): Unit = {
    out.puts
    out.puts("public override void _fetchInstances()")
    out.puts("{")
    out.inc
  }

  override def attrInvokeFetchInstances(baseExpr: expr, exprType: DataType, dataType: DataType): Unit = {
    val expr = castIfNeeded(expression(baseExpr), exprType, dataType)
    out.puts(s"$expr._fetchInstances();")
  }

  override def attrInvokeInstance(instName: InstanceIdentifier): Unit = {
    out.puts(s"_ = ${publicMemberName(instName)};")
  }

  override def writeHeader(endian: Option[FixedEndian]): Unit = {
    out.puts
    endian match {
      case Some(e) =>
        out.puts(s"private void _write_Seq${Utils.upperUnderscoreCase(e.toSuffix)}()")
      case None =>
        out.puts("public override void _write_Seq()")
    }
    out.puts("{")
    out.inc
  }

  override def checkHeader(): Unit = {
    out.puts
    out.puts("public override void _check()")
    out.puts("{")
    out.inc
  }

  override def writeInstanceHeader(instName: InstanceIdentifier): Unit = {
    out.puts
    out.puts(s"public void _write${idToSetterStr(instName)}()")
    out.puts("{")
    out.inc
    instanceClearWriteFlag(instName)
  }

  override def checkInstanceHeader(instName: InstanceIdentifier): Unit = {
    out.puts
    out.puts(s"public void _check${idToSetterStr(instName)}()")
    out.puts("{")
    out.inc
  }

  override def attributeDeclaration(attrName: Identifier, attrType: DataType, isNullable: Boolean): Unit = {
    out.puts(s"private ${kaitaiType2NativeTypeNullable(attrType, isNullable)} ${privateMemberName(attrName)};")
  }

  override def attributeReader(attrName: Identifier, attrType: DataType, isNullable: Boolean): Unit = {
    val addSetter = if (config.readWrite) s" set { ${privateMemberName(attrName)} = value; }" else ""
    out.puts(s"public ${kaitaiType2NativeTypeNullable(attrType, isNullable)} ${publicMemberName(attrName)} { get { return ${privateMemberName(attrName)}; }$addSetter }")
  }

  // The real setter is output in `attributeReader` above
  override def attributeSetter(attrName: Identifier, attrType: DataType, isNullable: Boolean): Unit = {}

  override def attrSetProperty(base: Ast.expr, propName: Identifier, value: String): Unit = {
    out.puts(s"${expression(base)}.${idToSetterStr(propName)} = ($value);")
  }
  override def universalDoc(doc: DocSpec): Unit = {
    out.puts
    doc.summary.foreach { summary =>
      out.puts("/// <summary>")
      out.putsLines("/// ", XMLUtils.escape(summary))
      out.puts("/// </summary>")
    }

    doc.ref.foreach { docRef =>
      out.puts("/// <remarks>")

      val refStr = docRef match {
        case TextRef(text) => XMLUtils.escape(text)
        case ref: UrlRef => ref.toAhref
      }

      out.putsLines("/// ", s"Reference: $refStr")
      out.puts("/// </remarks>")
    }
  }

  override def attrParseHybrid(leProc: () => Unit, beProc: () => Unit): Unit = {
    out.puts(s"if (${privateMemberName(EndianIdentifier)} == true) {")
    out.inc
    leProc()
    out.dec
    out.puts("} else {")
    out.inc
    beProc()
    out.dec
    out.puts("}")
  }

  override def attrProcess(proc: ProcessExpr, varSrc: Identifier, varDest: Identifier, rep: RepeatSpec): Unit = {
    val srcExpr = getRawIdExpr(varSrc, rep)

    val expr = proc match {
      case ProcessXor(xorValue) =>
        s"$normalIO.ProcessXor($srcExpr, ${expression(xorValue)})"
      case ProcessZlib =>
        s"$normalIO.ProcessZlib($srcExpr)"
      case ProcessRotate(isLeft, rotValue) =>
        val expr = if (isLeft) {
          expression(rotValue)
        } else {
          s"8 - (${expression(rotValue)})"
        }
        s"$normalIO.ProcessRotateLeft($srcExpr, $expr, 1)"
      case ProcessCustom(name, args) =>
        val procClass = types2class(name)
        val procName = s"_process_${idToStr(varSrc)}"
        out.puts(s"$procClass $procName = new $procClass(${args.map(expression).mkString(", ")});")
        s"$procName.Decode($srcExpr)"
    }
    handleAssignment(varDest, expr, rep, false)
  }

  override def attrUnprocess(proc: ProcessExpr, varSrc: Identifier, varDest: Identifier, rep: RepeatSpec, dataType: BytesType, exprTypeOpt: Option[DataType]): Unit = {
    val exprType = exprTypeOpt.getOrElse(dataType)
    val srcExprRaw = varSrc match {
      // use `_raw_items[_raw_items.size - 1]`
      case _: RawIdentifier => getRawIdExpr(varSrc, rep)
      // but `items[_index]`
      case _ => expression(itemExpr(varSrc, rep))
    }
    val srcExpr = castIfNeeded(srcExprRaw, exprType, dataType)

    val expr = proc match {
      case ProcessXor(xorValue) =>
        val argStr = if (inSubIOWriteBackHandler) "_processXorArg" else expression(xorValue)
        val xorValueStr = translator.detectType(xorValue) match {
          case _: IntType => castIfNeeded(argStr, AnyType, Int1Type(true))
          case _ => argStr
        }
        s"$normalIO.ProcessXor($srcExpr, $xorValueStr)"
      case ProcessZlib => 
        s"$normalIO.UnprocessZlib($srcExpr)"
      case ProcessRotate(isLeft, rotValue) =>
        val argStr = if (inSubIOWriteBackHandler) "_processRotateArg" else expression(rotValue)
        val expr = if (!isLeft) {
          argStr
        } else {
          s"8 - ($argStr)"
        }
        s"$normalIO.ProcessRotateLeft($srcExpr, $expr, 1)"
      case ProcessCustom(name, args) =>
        val namespace = name.init.mkString(".")
        val procClass = namespace +
          (if (namespace.nonEmpty) "." else "") +
          type2class(name.last)
        val procName = s"_process_${idToStr(varSrc)}"
        if (!inSubIOWriteBackHandler) {
          out.puts(s"$procClass $procName = new $procClass(${args.map(expression).mkString(", ")});")
        }
        s"$procName.encode($srcExpr)"
    }
    handleAssignment(varDest, expr, rep, false)
  }

  override def attrUnprocessPrepareBeforeSubIOHandler(proc: ProcessExpr, varSrc: Identifier): Unit = {
    proc match {
      case ProcessXor(xorValue) =>
        val dataType = translator.detectType(xorValue)
        out.puts(s"${kaitaiType2NativeType(dataType)} _processXorArg = ${expression(xorValue)};")
      case ProcessRotate(_, rotValue) =>
        val dataType = translator.detectType(rotValue)
        out.puts(s"${kaitaiType2NativeType(dataType)} _processRotateArg = ${expression(rotValue)};")
      case ProcessZlib => // no process arguments
      case ProcessCustom(name, args) =>
        val namespace = name.init.mkString(".")
        val procClass = namespace +
          (if (namespace.nonEmpty) "." else "") +
          type2class(name.last)
        val procName = s"_process_${idToStr(varSrc)}"
        out.puts(s"$procClass $procName = new $procClass(${args.map(expression).mkString(", ")});")
    }
  }

  override def allocateIO(varName: Identifier, rep: RepeatSpec): String = {
    val privateVarName = privateMemberName(varName)

    val ioName = s"io_$privateVarName"

    val args = rep match {
      case RepeatUntil(_) => translator.doName(Identifier.ITERATOR2)
      case _ => getRawIdExpr(varName, rep)
    }

    out.puts(s"var $ioName = new $kstreamName($args);")
    ioName
  }

  override def allocateIOFixed(varName: Identifier, size: String): String = {
    val privateVarName = privateMemberName(varName)

    val ioName = s"_io_$privateVarName"

    out.puts(s"$kstreamName $ioName = new KaitaiStream($size);")
    ioName
  }

  override def exprIORemainingSize(io: String): String =
    s"$io.Size - $io.Pos"
  
  override def allocateIOGrowing(varName: Identifier): String =
    allocateIOFixed(varName, "100000") // FIXME to use real growing buffer
  
  override def subIOWriteBackHeader(subIO: String): String = {
    val parentIoName = "parent"
    out.puts(s"${type2class(typeProvider.nowClass.name.last)} _this = this;")
    out.puts(s"$subIO.SetWriteBackHandler(new $kstreamName.WriteBackHandler(_pos2, $parentIoName => {")
    out.inc

    inSubIOWriteBackHandler = true

    parentIoName
  }

  override def subIOWriteBackFooter: Unit = {
    inSubIOWriteBackHandler = false

    out.dec
    out.puts("}));")
  }

  override def addChildIO(io: String, childIO: String): Unit =
    out.puts(s"$io.AddChildStream($childIO);")

  def getRawIdExpr(varName: Identifier, rep: RepeatSpec): String = {
    val memberName = privateMemberName(varName)
    rep match {
      case NoRepeat => memberName
      case _ => s"$memberName[$memberName.Count - 1]"
    }
  }

  override def useIO(ioEx: expr): String = {
    out.puts(s"$kstreamName io = ${expression(ioEx)};")
    "io"
  }

  override def pushPos(io: String): Unit =
    out.puts(s"long _pos = $io.Pos;")

  override def pushPosForSubIOWriteBackHandler(io: String): Unit =
    out.puts(s"long _pos2 = $io.Pos;")

  override def seek(io: String, pos: Ast.expr): Unit =
    out.puts(s"$io.Seek(${expression(pos)});")

  override def seekRelative(io: String, relPos: String): Unit =
    out.puts(s"$io.Seek($io.Pos + ($relPos));")

  override def popPos(io: String): Unit =
    out.puts(s"$io.Seek(_pos);")

  // NOTE: the compiler does not need to output alignToByte() calls for C# anymore, since the byte
  // alignment is handled by the runtime library
  override def alignToByte(io: String): Unit = {}

  override def instanceClear(instName: InstanceIdentifier): Unit = {
    out.puts(s"_hasRead_${idToStr(instName)} = false;")
  }

  override def instanceSetCalculated(instName: InstanceIdentifier): Unit = {
    out.puts(s"_hasRead_${idToStr(instName)} = true;")
  }

  override def condIfHeader(expr: expr): Unit = {
    out.puts(s"if (${expression(expr)})")
    out.puts("{")
    out.inc
  }

  override def condRepeatCommonInit(id: Identifier, dataType: DataType, needRaw: NeedRaw): Unit = {
    importList.add("System.Collections.Generic")

    if (needRaw.level >= 1)
      out.puts(s"${privateMemberName(RawIdentifier(id))} = new List<byte[]>();")
    if (needRaw.level >= 2)
      out.puts(s"${privateMemberName(RawIdentifier(RawIdentifier(id)))} = new List<byte[]>();")
    if (config.readWrite) {
      dataType match {
        case utb: UserTypeFromBytes =>
          if (writeNeedsOuterSize(utb))
            out.puts(s"${privateMemberName(OuterSizeIdentifier(id))} = new List<int>();")
          if (writeNeedsInnerSize(utb))
            out.puts(s"${privateMemberName(InnerSizeIdentifier(id))} = new List<int>();")
        case _ => // do nothing
      }
    }
    out.puts(s"${privateMemberName(id)} = new ${kaitaiType2NativeType(ArrayTypeInStream(dataType))}();")
  }

  override def condRepeatCommonWriteInit(id: Identifier, dataType: DataType, needRaw: NeedRaw): Unit = {
    if (needRaw.level >= 1)
      out.puts(s"${privateMemberName(RawIdentifier(id))} = new List<byte[]>();")
    if (needRaw.level >= 2)
      out.puts(s"${privateMemberName(RawIdentifier(RawIdentifier(id)))} = new List<byte[]>();")
  }

  override def condRepeatEosHeader(id: Identifier, io: String, dataType: DataType): Unit = {
    out.puts("{")
    out.inc
    out.puts("var i = 0;")
    out.puts(s"while (!$io.IsEof) {")
    out.inc
  }

  override def handleAssignmentRepeatEos(id: Identifier, expr: String): Unit = {
    out.puts(s"${privateMemberName(id)}.Add($expr);")
  }

  override def condRepeatEosFooter: Unit = {
    out.puts("i++;")
    out.dec
    out.puts("}")
    out.dec
    out.puts("}")
  }

  override def condRepeatExprHeader(id: Identifier, io: String, dataType: DataType, repeatExpr: expr): Unit = {
    out.puts(s"for (var i = 0; i < ${expression(repeatExpr)}; i++)")
    out.puts("{")
    out.inc
  }

  // used for all repetitions in _check()
  override def condRepeatCommonHeader(id: Identifier, io: String, dataType: DataType): Unit = {
    out.puts(s"for (var i = 0; i < ${privateMemberName(id)}.Count(); i++)")
    out.puts("{")
    out.inc
  }

  override def handleAssignmentRepeatExpr(id: Identifier, expr: String): Unit =
    handleAssignmentRepeatEos(id, expr)

  override def condRepeatUntilHeader(id: Identifier, io: String, dataType: DataType, untilExpr: expr): Unit = {
    out.puts("{")
    out.inc
    out.puts("var i = 0;")
    out.puts(s"${kaitaiType2NativeType(dataType)} ${translator.doName(Identifier.ITERATOR)};")
    out.puts("do {")
    out.inc
  }

  override def handleAssignmentRepeatUntil(id: Identifier, expr: String, isRaw: Boolean): Unit = {
    val (typeDecl, tempVar) = if (isRaw) {
      ("byte[] ", translator.doName(Identifier.ITERATOR2))
    } else {
      ("", translator.doName(Identifier.ITERATOR))
    }
    out.puts(s"$typeDecl$tempVar = $expr;")
    out.puts(s"${privateMemberName(id)}.Add($tempVar);")
  }

  override def condRepeatUntilFooter(id: Identifier, io: String, dataType: DataType, untilExpr: expr): Unit = {
    typeProvider._currentIteratorType = Some(dataType)
    out.puts("i++;")
    out.dec
    out.puts(s"} while (!(${expression(untilExpr)}));")
    out.dec
    out.puts("}")
  }

  override def handleAssignmentSimple(id: Identifier, expr: String): Unit =
    out.puts(s"${privateMemberName(id)} = $expr;")

  override def handleAssignmentTempVar(dataType: DataType, id: String, expr: String): Unit =
    out.puts(s"${kaitaiType2NativeType(dataType)} $id = $expr;")

  override def blockScopeHeader: Unit = {
    out.puts("{")
    out.inc
  }
  override def blockScopeFooter: Unit = {
    out.dec
    out.puts("}")
  }

  override def parseExpr(dataType: DataType, assignType: DataType, io: String, defEndian: Option[FixedEndian]): String = {
    dataType match {
      case t: ReadableType =>
        s"$io.Read${Utils.capitalize(t.apiCall(defEndian))}()"
      case blt: BytesLimitType =>
        s"$io.ReadBytes(${expression(blt.size)})"
      case _: BytesEosType =>
        s"$io.ReadBytesFull()"
      case BytesTerminatedType(terminator, include, consume, eosError, _) =>
        s"$io.ReadBytesTerm($terminator, $include, $consume, $eosError)"
      case BitsType1(bitEndian) =>
        s"$io.ReadBitsInt${Utils.upperCamelCase(bitEndian.toSuffix)}(1) != 0"
      case BitsType(width: Int, bitEndian) =>
        s"$io.ReadBitsInt${Utils.upperCamelCase(bitEndian.toSuffix)}($width)"
      case t: UserType =>
        val addParams = Utils.join(t.args.map((a) => translator.translate(a)), "", ", ", ", ")
        val addArgs = if (t.isOpaque) {
          ""
        } else {
          val parent = t.forcedParent match {
            case Some(USER_TYPE_NO_PARENT) => "null"
            case Some(fp) => translator.translate(fp)
            case None => "this"
          }
          val addEndian = t.classSpec.get.meta.endian match {
            case Some(InheritedEndian) => s", ${privateMemberName(EndianIdentifier)}"
            case _ => ""
          }
          s", $parent, ${privateMemberName(RootIdentifier)}$addEndian"
        }
        s"new ${types2class(t.name)}($addParams$io$addArgs)"
    }
  }

  override def bytesPadTermExpr(expr0: String, padRight: Option[Int], terminator: Option[Int], include: Boolean) = {
    val expr1 = padRight match {
      case Some(padByte) if terminator.map(term => padByte != term).getOrElse(true) =>
        s"$kstreamName.BytesStripRight($expr0, $padByte)"
      case _ => expr0
    }
    val expr2 = terminator match {
      case Some(term) => s"$kstreamName.BytesTerminate($expr1, $term, $include)"
      case None => expr1
    }
    expr2
  }

  override def userTypeDebugRead(id: String, dataType: DataType, assignType: DataType): Unit = {
    val expr = castIfNeeded(id, assignType, dataType)
    out.puts(s"$expr._read();")
  }

  override def switchRequiresIfs(onType: DataType): Boolean = onType match {
    case _: IntType | _: EnumType | _: StrType => false
    case _ => true
  }

  //<editor-fold desc="switching: true version">

  val NAME_SWITCH_ON = Ast.expr.Name(Ast.identifier(Identifier.SWITCH_ON))

  override def switchStart(id: Identifier, on: Ast.expr): Unit =
    out.puts(s"switch (${expression(on)}) {")

  override def switchCaseFirstStart(condition: Ast.expr): Unit = switchCaseStart(condition)

  override def switchCaseStart(condition: Ast.expr): Unit = {
    out.puts(s"case ${expression(condition)}: {")
    out.inc
  }

  override def switchCaseEnd(): Unit = {
    out.puts("break;")
    out.dec
    out.puts("}")
  }

  override def switchElseStart(): Unit = {
    out.puts("default: {")
    out.inc
  }

  override def switchEnd(): Unit =
    out.puts("}")

  //</editor-fold>

  //<editor-fold desc="switching: emulation with ifs">

  override def switchIfStart(id: Identifier, on: Ast.expr, onType: DataType): Unit = {
    out.puts("{")
    out.inc
    out.puts(s"${kaitaiType2NativeType(onType)} ${expression(NAME_SWITCH_ON)} = ${expression(on)};")
  }

  def switchCmpExpr(condition: Ast.expr): String =
    expression(
      Ast.expr.Compare(
        NAME_SWITCH_ON,
        Ast.cmpop.Eq,
        condition
      )
    )

  override def switchIfCaseFirstStart(condition: Ast.expr): Unit = {
    out.puts(s"if (${switchCmpExpr(condition)})")
    out.puts("{")
    out.inc
  }

  override def switchIfCaseStart(condition: Ast.expr): Unit = {
    out.puts(s"else if (${switchCmpExpr(condition)})")
    out.puts("{")
    out.inc
  }

  override def switchIfCaseEnd(): Unit = {
    out.dec
    out.puts("}")
  }

  override def switchIfElseStart(): Unit = {
    out.puts("else")
    out.puts("{")
    out.inc
  }

  override def switchIfEnd(): Unit = {
    out.dec
    out.puts("}")
  }

  //</editor-fold>

  override def instanceDeclaration(attrName: InstanceIdentifier, attrType: DataType, isNullable: Boolean): Unit = {
    out.puts(s"private ${kaitaiType2NativeTypeNullable(attrType, isNullable)} ${privateMemberName(attrName)};")
    out.puts(s"private bool _hasRead_${idToStr(attrName)};")
  }

  override def instanceWriteFlagDeclaration(attrName: InstanceIdentifier): Unit = {
    out.puts(s"private bool _shouldWrite_${idToSetterStr(attrName)} = false;")
    out.puts(s"private bool _toWrite${idToSetterStr(attrName)} = true;")
  }

  override def instanceSetWriteFlag(instName: InstanceIdentifier): Unit = {
    out.puts(s"_shouldWrite_${idToSetterStr(instName)} = _toWrite${idToSetterStr(instName)};")
  }

  override def instanceClearWriteFlag(instName: InstanceIdentifier): Unit = {
    out.puts(s"_shouldWrite_${idToSetterStr(instName)} = false;")
  }

  override def instanceToWriteSetter(instName: InstanceIdentifier): Unit = {
    out.puts(s"public void Set${idToSetterStr(instName)}_ToWrite(bool _v) { _toWrite${idToSetterStr(instName)} = _v; }")
  }

  override def instanceHeader(className: String, instName: InstanceIdentifier, dataType: DataType, isNullable: Boolean): Unit = {
    out.puts(s"public ${kaitaiType2NativeTypeNullable(dataType, isNullable)} ${publicMemberName(instName)}")
    out.puts("{")
    out.inc
    out.puts("get")
    out.puts("{")
    out.inc
  }

  override def instanceFooter(className: List[String], instName: InstanceIdentifier, dataType: DataType, isNullable: Boolean, shouldAddSetter: Boolean): Unit = {
    out.dec
    out.puts("}")

    // FIXME: this shouldn't be here, and the entire overload of `instanceFooter` with
    // parameters should be removed from LanguageCompiler
    if (config.readWrite && shouldAddSetter) {
      out.puts("set")
      out.puts("{")
      out.inc

      out.puts(s"${privateMemberName(instName)} = value;")
      instanceSetCalculated(instName)

      out.dec
      out.puts("}")
    }

    out.dec
    out.puts("}")
  }

  override def instanceCheckCacheAndReturn(instName: InstanceIdentifier, dataType: DataType): Unit = {
    out.puts(s"if (_hasRead_${idToStr(instName)})")
    out.inc
    instanceReturn(instName, dataType)
    out.dec
  }

  override def instanceCheckWriteFlagAndWrite(instName: InstanceIdentifier): Unit = {
    out.puts(s"if (_shouldWrite_${idToSetterStr(instName)})")
    out.inc
    out.puts(s"_write${idToSetterStr(instName)}();")
    out.dec
  }

  override def instanceReturn(instName: InstanceIdentifier, attrType: DataType): Unit = {
    out.puts(s"return ${privateMemberName(instName)};")
  }

  override def instanceCalculate(instName: Identifier, dataType: DataType, value: expr): Unit =
    // Perform explicit cast as unsigned integers can't be directly assigned to the default int type
    handleAssignmentSimple(instName, s"(${kaitaiType2NativeType(dataType)}) (${expression(value)})")

  override def instanceInvalidate(instName: InstanceIdentifier): Unit = {
    out.puts(s"public void _invalidate${idToSetterStr(instName)}() { _hasRead_${idToStr(instName)} = false; }")
  }

  override def enumDeclaration(curClass: String, enumName: String, enumColl: Seq[(Long, String)]): Unit = {
    val enumClass = type2class(enumName)

    out.puts
    out.puts(s"public enum $enumClass")
    out.puts(s"{")
    out.inc

    enumColl.foreach { case (id, label) =>
      out.puts(s"${Utils.upperCamelCase(label)} = ${translator.doIntLiteral(id)},")
    }

    out.dec
    out.puts("}")
  }

  override def internalEnumIntType(basedOn: IntType): DataType = {
    basedOn match {
      case IntMultiType(signed, _, endian) => IntMultiType(signed, Width8, endian)
      case _ => IntMultiType(true, Width8, None)
    }
  }

  override def attrPrimitiveWrite(
    io: String,
    valueExpr: Ast.expr,
    dataType: DataType,
    defEndian: Option[FixedEndian],
    exprTypeOpt: Option[DataType]
  ): Unit = {
    val exprType = exprTypeOpt.getOrElse(dataType)
    val exprRaw = expression(valueExpr)
    val expr = s"((${kaitaiType2NativeType(dataType)}) ($exprRaw))"

    val stmt = dataType match {
      case t: ReadableType =>
        s"$io.Write${Utils.capitalize(t.apiCall(defEndian))}($expr)"
      case BitsType1(bitEndian) =>
        s"$io.WriteBitsInt${Utils.upperCamelCase(bitEndian.toSuffix)}(1, (ulong)${translator.boolToInt(valueExpr)})"
      case BitsType(width: Int, bitEndian) =>
        s"$io.WriteBitsInt${Utils.upperCamelCase(bitEndian.toSuffix)}($width, $expr)"
      case _: BytesType =>
        s"$io.WriteBytes($expr)"
    }
    out.puts(stmt + ";")
  }

  override def attrBytesLimitWrite(io: String, expr: Ast.expr, size: String, term: Int, padRight: Int): Unit =
    out.puts(s"$io.WriteBytesLimit(${expression(expr)}, $size, (byte) $term, (byte) $padRight);")
  
  override def attrUserTypeInstreamWrite(io: String, valueExpr: Ast.expr, dataType: DataType, exprType: DataType): Unit = {
    val exprRaw = expression(valueExpr)
    var expr = castIfNeeded(exprRaw, exprType, dataType)
    out.puts(s"$expr._write_Seq($io);")
  }

  override def attrWriteStreamToStream(srcIo: String, dstIo: String) =
    out.puts(s"$dstIo.WriteStream($srcIo);")
  
  override def exprStreamToByteArray(io: String): String =
    s"$io.ToByteArray()"
  
  override def attrBasicCheck(checkExpr: Ast.expr, actual: Ast.expr, expected: Ast.expr, msg: String): Unit = {
    val msgStr = expression(Ast.expr.Str(msg))

    out.puts(s"if (${expression(checkExpr)})")
    out.inc
    out.puts(s"throw new ConsistencyError($msgStr, ${expression(actual)}, ${expression(expected)});")
    out.dec
  }

  override def attrObjectsEqualCheck(actual: Ast.expr, expected: Ast.expr, msg: String): Unit = {
    val msgStr = expression(Ast.expr.Str(msg))

    out.puts(s"if (!object.Equals(${expression(actual)}, ${expression(expected)}))")
    out.inc
    out.puts(s"throw new ConsistencyError($msgStr, ${expression(actual)}, ${expression(expected)});")
    out.dec
  }

  override def attrParentParamCheck(actualParentExpr: Ast.expr, ut: UserType, shouldDependOnIo: Option[Boolean], msg: String): Unit = {
    if (ut.isOpaque)
      return
    
    /** @note Must be kept in sync with [[CSharpCompiler.parseExpr]] */
    val (expectedParent, dependsOnIo) = ut.forcedParent match {
      case Some(USER_TYPE_NO_PARENT) => ("null", false)
      case Some(fp) =>
        (expression(fp), userExprDependsOnIo(fp))
      case None => ("this", false)
    }
    if (shouldDependOnIo.map(shouldDepend => dependsOnIo != shouldDepend).getOrElse(false))
      return
    
    val msgStr = expression(Ast.expr.Str(msg))

    out.puts(s"if (!object.Equals(${expression(actualParentExpr)}, $expectedParent))")
    out.inc
    out.puts(s"throw new ConsistencyError($msgStr, ${expression(actualParentExpr)}, $expectedParent);")
    out.dec
  }

  override def attrIsEofCheck(io: String, expectedIsEof: Boolean, msg: String): Unit = {
    val msgStr = expression(Ast.expr.Str(msg))

    val eofExpr = s"$io.IsEof"
    val ifExpr = if (expectedIsEof) {
      s"!($eofExpr)"
    } else {
      eofExpr
    }
    out.puts(s"if ($ifExpr)")
    out.inc
    out.puts(s"throw new ConsistencyError($msgStr, ${exprIORemainingSize(io)}, 0);")
    out.dec
  }

  override def condIfIsEofHeader(io: String, wantedIsEof: Boolean): Unit = {
    val eofExpr = s"$io.IsEof"
    val ifExpr = if (!wantedIsEof) {
      s"!($eofExpr)"
    } else {
      eofExpr
    }

    out.puts(s"if ($ifExpr)")
    out.puts("{")
    out.inc
  }

  override def condIfIsEofFooter: Unit = fileFooter("")

  override def idToStr(id: Identifier): String = CSharpCompiler.idToStr(id)

  override def publicMemberName(id: Identifier): String = CSharpCompiler.publicMemberName(id)

  def idToSetterStr(id: Identifier): String = {
    id match {
      case SpecialIdentifier(name) => name
      case NamedIdentifier(name) => Utils.upperCamelCase(name)
      case NumberedIdentifier(idx) => s"_${NumberedIdentifier.TEMPLATE}$idx"
      case InstanceIdentifier(name) => Utils.upperCamelCase(name)
      case RawIdentifier(innerId) => "_raw_" + idToSetterStr(innerId)
      case OuterSizeIdentifier(innerId) => s"${idToSetterStr(innerId)}_OuterSize"
      case InnerSizeIdentifier(innerId) => s"${idToSetterStr(innerId)}_InnerSize"
    }
  }

  override def privateMemberName(id: Identifier): String = {
    id match {
      case SpecialIdentifier(name) => s"m${Utils.lowerCamelCase(name)}"
      case _ => s"_${idToStr(id)}"
    }
  }

  override def localTemporaryName(id: Identifier): String = s"_t_${idToStr(id)}"

  override def paramName(id: Identifier): String = s"p_${idToStr(id)}"

  override def ksErrorName(err: KSError): String = CSharpCompiler.ksErrorName(err)

  override def attrValidateExpr(
    attrId: Identifier,
    attrType: DataType,
    checkExpr: Ast.expr,
    err: KSError,
    errArgs: List[Ast.expr]
  ): Unit = {
    val errArgsStr = errArgs.map(translator.translate).mkString(", ")
    out.puts(s"if (!(${translator.translate(checkExpr)}))")
    out.puts("{")
    out.inc
    out.puts(s"throw new ${ksErrorName(err)}($errArgsStr);")
    out.dec
    out.puts("}")
  }

  def kstructNameFull: String = {
    ((config.autoRead, config.readWrite) match {
      case (_, true) => "ReadWrite"
      case (false, false) => "ReadOnly"
      case (true, false) => ""
    }) + kstructName
  }

  def castIfNeeded(exprRaw: String, exprType: DataType, targetType: DataType): String =
    if (exprType != targetType) {
      val castTypeId = kaitaiType2NativeType(targetType)
      s"(($castTypeId) ($exprRaw))"
    } else {
      exprRaw
    }

  /**
    * Determine .NET data type corresponding to a KS data type.
    *
    * @param attrType KS data type
    * @return .NET data type
    */
  def kaitaiType2NativeType(attrType: DataType): String = {
    attrType match {
      case Int1Type(false) => "byte"
      case IntMultiType(false, Width2, _) => "ushort"
      case IntMultiType(false, Width4, _) => "uint"
      case IntMultiType(false, Width8, _) => "ulong"

      case Int1Type(true) => "sbyte"
      case IntMultiType(true, Width2, _) => "short"
      case IntMultiType(true, Width4, _) => "int"
      case IntMultiType(true, Width8, _) => "long"

      case FloatMultiType(Width4, _) => "float"
      case FloatMultiType(Width8, _) => "double"

      case BitsType(_, _) => "ulong"

      case CalcIntType => "int"
      case CalcFloatType => "double"
      case _: BooleanType => "bool"

      case _: StrType => "string"
      case _: BytesType => "byte[]"

      case AnyType => "object"
      case KaitaiStructType | CalcKaitaiStructType => kstructNameFull
      case KaitaiStreamType | OwnedKaitaiStreamType => kstreamName

      case t: UserType => types2class(t.name)
      case EnumType(name, _) => types2class(name)

      case at: ArrayType => s"List<${kaitaiType2NativeType(at.elType)}>"

      case st: SwitchType => kaitaiType2NativeType(st.combinedType)
    }
  }

  def kaitaiType2NativeTypeNullable(t: DataType, isNullable: Boolean): String = {
    val r = kaitaiType2NativeType(t)
    if (isNullable) {
      t match {
        case _: NumericType | _: BooleanType => s"$r?"
        case _ => r
      }
    } else {
      r
    }
  }
}

object CSharpCompiler extends LanguageCompilerStatic
  with StreamStructNames
  with UpperCamelCaseClasses
  with ExceptionNames {
  override def getCompiler(
    tp: ClassTypeProvider,
    config: RuntimeConfig
  ): LanguageCompiler = new CSharpCompiler(tp, config)
  
  def publicMemberName(id: Identifier): String =
    id match {
      case SpecialIdentifier(name) => s"M${Utils.upperCamelCase(name)}"
      case NamedIdentifier(name) => Utils.upperCamelCase(name)
      case NumberedIdentifier(idx) => s"${NumberedIdentifier.TEMPLATE.capitalize}_$idx"
      case InstanceIdentifier(name) => Utils.upperCamelCase(name)
      case RawIdentifier(innerId) => s"M_Raw${publicMemberName(innerId)}"
      case OuterSizeIdentifier(innerId) => s"${idToStr(innerId)}_OuterSize"
      case InnerSizeIdentifier(innerId) => s"${idToStr(innerId)}_InnerSize"
    }

  def idToStr(id: Identifier): String =
    id match {
      case SpecialIdentifier(name) => name
      case NamedIdentifier(name) => Utils.lowerCamelCase(name)
      case NumberedIdentifier(idx) => s"_${NumberedIdentifier.TEMPLATE}$idx"
      case InstanceIdentifier(name) => Utils.lowerCamelCase(name)
      case RawIdentifier(innerId) => s"_raw_${idToStr(innerId)}"
      case OuterSizeIdentifier(innerId) => s"${idToStr(innerId)}_outerSize"
      case InnerSizeIdentifier(innerId) => s"${idToStr(innerId)}_innerSize"
    }

  def types2class(typeName: Ast.typeId): String =
    // FIXME: handle absolute
    types2class(typeName.names)
  def types2class(names: Iterable[String]) = names.map(type2class).mkString(".")

  override def kstructName = "KaitaiStruct"
  override def kstreamName = "KaitaiStream"
  override def ksErrorName(err: KSError): String = err match {
    case EndOfStreamError => "EndOfStreamException"
    case _ => err.name
  }
}
