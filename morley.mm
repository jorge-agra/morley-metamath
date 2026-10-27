$( Morley's trisector theorem in the complex plane, by Connes' rotations.
   The theorem is morleyR2. See docs/statement.md and docs/proof.md.
   Original publication material is dedicated under CC0 1.0.
   This extension introduces no new axioms. $)

$[ set.mm $]


  $( The sine of the argument of a nonzero complex number ` A ` is the
     imaginary part of the unit vector ` ( A / ( abs `` A ) ) ` .  The argument
     is written ` ( Im `` ( log `` A ) ) ` , as in ~ efiarg .  (Contributed by
     JAG, 13-Oct-2026.) $)
  sinarg $p |- ( ( A e. CC /\ A =/= 0 ) -> ( sin ` ( Im ` ( log ` A ) ) )
      = ( Im ` ( A / ( abs ` A ) ) ) ) $=
    ( cc wcel cc0 wne wa clog cfv csin ci cmul co ce cabs cdiv wceq logcl imcld
    cim cr resinval syl efiarg fveq2d eqtrd ) ABCADEFAGHSHIHJAGHSHKLMHSHAANHOLS
    HABCADEFAGHSHTCAGHSHIHJAGHSHKLMHSHPABCADEFAGHAQRAGHSHUAUBABCADEFJAGHSHKLMHA
    ANHOLSAUCUDUE $.


  $( Division by a nonzero complex number ` A ` is multiplication by its
     conjugate followed by division by the square of its absolute value.
     (Contributed by JAG, 13-Oct-2026.) $)
  divcjabs2 $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ B e. CC ) -> ( B / A )
      = ( ( ( * ` A ) x. B ) / ( ( abs ` A ) ^ 2 ) ) ) $=
    ( cc wcel cc0 wne wa ccj cmul co cdiv cabs c2 cexp simpr simpll cjcld simpl
    cfv simprd cjne0d divcan5d absvalsqd mulcomd eqtrd eqcomd oveq2d eqtr3d ) A
    CDAEFGBCDGAHSBIJAHSAIJKJBAKJAHSBIJALSMNJKJACDAEFGBCDGBAAHSACDAEFGBCDOACDAEF
    BCDPACDAEFGBCDGAACDAEFBCDPQACDAEFGBCDGACDAEFACDAEFGBCDRTACDAEFGBCDGAACDAEFB
    CDPACDAEFGBCDGACDAEFACDAEFGBCDRTUAUBACDAEFGBCDGAHSAIJALSMNJAHSBIJKACDAEFGBC
    DGALSMNJAHSAIJACDAEFGBCDGALSMNJAAHSIJAHSAIJACDAEFGBCDGAACDAEFBCDPUCACDAEFGB
    CDGAAHSACDAEFBCDPACDAEFGBCDGAACDAEFBCDPQUDUEUFUGUH $.


  $( The imaginary part of a quotient ` ( B / A ) ` of complex numbers is the
     imaginary part of ` ( ( * `` A ) x. B ) ` divided by the square of the
     absolute value of ` A ` .  See ~ divcjabs2 .  (Contributed by JAG,
     13-Oct-2026.) $)
  imdivcjabs2 $p |- ( ( ( A e. CC /\ A =/= 0 ) /\ B e. CC )
      -> ( Im ` ( B / A ) )
      = ( ( Im ` ( ( * ` A ) x. B ) ) / ( ( abs ` A ) ^ 2 ) ) ) $=
    ( cc wcel cc0 wne wa cdiv co cim cfv ccj cmul cabs c2 cexp divcjabs2 fveq2d
    simpll abscld resqcld cjcld simpr mulcld simpl simprd wb recnd sqne0 mpbird
    absne0d syl imdivd eqtrd ) ACDAEFGBCDGBAHIJKALKBMIANKOPIHIJKALKBMIJKANKOPIH
    IACDAEFGBCDGBAHIALKBMIANKOPIHIJABQRACDAEFGBCDGANKOPIALKBMIACDAEFGBCDGANKACD
    AEFGBCDGAACDAEFBCDSTUAACDAEFGBCDGALKBACDAEFGBCDGAACDAEFBCDSUBACDAEFGBCDUCUD
    ACDAEFGBCDGANKOPIEFANKEFACDAEFGBCDGAACDAEFBCDSACDAEFGBCDGACDAEFACDAEFGBCDUE
    UFUKACDAEFGBCDGANKCDANKOPIEFANKEFUGACDAEFGBCDGANKACDAEFGBCDGAACDAEFBCDSTUHA
    NKUIULUJUMUN $.


  $( The imaginary part of ` ( ( * `` A ) x. B ) ` is the determinant of the
     real and imaginary parts of ` A ` and ` B ` , that is, twice the signed
     area of the triangle with vertices ` 0 ` , ` A ` and ` B ` .  (Contributed
     by JAG, 13-Oct-2026.) $)
  imcjmul $p |- ( ( A e. CC /\ B e. CC ) -> ( Im ` ( ( * ` A ) x. B ) )
      = ( ( ( Re ` A ) x. ( Im ` B ) ) - ( ( Im ` A ) x. ( Re ` B ) ) ) ) $=
    ( cc wcel wa ccj cfv cmul co cim cre caddc wceq simpl simpr syl imcld recnd
    cneg recld cmin cjcld immul recj oveq1d imcj mulneg1d eqtrd oveq12d negsubd
    jca mulcld ) ACDBCDEAFGBHIJGAFGKGBJGHIAFGJGBKGHILIAKGBJGHIAJGBKGHIUAIACDBCD
    EAFGCDBCDEAFGBHIJGAFGKGBJGHIAFGJGBKGHILIMACDBCDEAFGCDBCDACDBCDEAACDBCDNUBAC
    DBCDOUKAFGBUCPACDBCDEAFGKGBJGHIAFGJGBKGHILIAKGBJGHIAJGBKGHISLIAKGBJGHIAJGBK
    GHIUAIACDBCDEAFGKGBJGHIAKGBJGHIAFGJGBKGHIAJGBKGHISLACDBCDEAFGKGAKGBJGHACDBC
    DEACDAFGKGAKGMACDBCDNAUDPUEACDBCDEAFGJGBKGHIAJGSBKGHIAJGBKGHISACDBCDEAFGJGA
    JGSBKGHACDBCDEACDAFGJGAJGSMACDBCDNAUFPUEACDBCDEAJGBKGACDBCDEAJGACDBCDEAACDB
    CDNQRACDBCDEBKGACDBCDEBACDBCDOTRUGUHUIACDBCDEAKGBJGHIAJGBKGHIACDBCDEAKGBJGA
    CDBCDEAKGACDBCDEAACDBCDNTRACDBCDEBJGACDBCDEBACDBCDOQRULACDBCDEAJGBKGACDBCDE
    AJGACDBCDEAACDBCDNQRACDBCDEBKGACDBCDEBACDBCDOTRULUJUHUH $.


  $( Adding the first row of a two-by-two determinant to its second row leaves
     the determinant unchanged: with rows ` A ` , ` B ` and ` C ` , ` D ` , the
     determinant ` ( ( A x. D ) - ( B x. C ) ) ` equals the one with rows
     ` A ` , ` B ` and ` ( A + C ) ` , ` ( B + D ) ` .  (Contributed by JAG,
     13-Oct-2026.) $)
  detaddsub $p |- ( ( ( A e. CC /\ B e. CC ) /\ ( C e. CC /\ D e. CC ) )
      -> ( ( A x. ( B + D ) ) - ( B x. ( A + C ) ) )
      = ( ( A x. D ) - ( B x. C ) ) ) $=
    ( cc wcel wa caddc co cmul cmin cc0 simpll adddid mulcl mulcld oveq1d eqtrd
    jca syl simplr simprr simprl oveq12d addsub4d mulcomd eqcomd subidd addlidd
    3eqtrd subcld ) AEFZBEFZGZCEFZDEFZGZGZABDHIJIZBACHIJIZKIZLADJIZBCJIZKIZHIZV
    DURVAABJIZVBHIZBAJIZVCHIZKIVFVHKIZVDHIVEURUSVGUTVIKURABDULUMUQMZULUMUQUAZUN
    UOUPUBZNURBACVLVKUNUOUPUCZNUDURVFVBVHVCURUNVFEFURULUMVKVLSABOTURADVKVMPZURU
    MULGVHEFURUMULVLVKSBAOTZURBCVLVNPZUEURVJLVDHURVJVHVHKILURVFVHVHKURVHVFURBAV
    LVKUFUGQURVHVPUHRQUJURVDURVBVCVOVQUKUIR $.


  $( Twice the signed area of a triangle given by coordinates is the same
     whether it is computed from the first vertex or from the second.  The
     vertices have coordinates ` A ` , ` B ` , then ` C ` , ` D ` , then
     ` E ` , ` F ` ; each side of the equation is a determinant of coordinate
     differences.  (Contributed by JAG, 13-Oct-2026.) $)
  det3cyc $p |- ( ( ( A e. CC /\ B e. CC /\ C e. CC )
      /\ ( D e. CC /\ E e. CC /\ F e. CC ) )
      -> ( ( ( C - A ) x. ( F - B ) ) - ( ( D - B ) x. ( E - A ) ) )
      = ( ( ( E - C ) x. ( B - D ) ) - ( ( F - D ) x. ( A - C ) ) ) ) $=
    ( cc wcel wa cmin co cmul cneg caddc subcld 3eqtrd eqcomd oveq12d eqtrd jca
    simpl3 simpl1 negcld simpr2 addcomd negsubd simpr1 simpl2 negsubdi2d addcld
    w3a nnncan2d mulcomd simpr3 wceq detaddsub syl mulneg1d mulcld neg2subd ) A
    GHZBGHZCGHZUKZDGHZEGHZFGHZUKZIZECJKZBDJKZLKZFDJKZACJKZLKZJKZCAJKZFBJKZLKZDB
    JKZEAJKZLKZJKZVIVPVTMZWALKZVQMZVRLKZJKZWBMZVSMZJKWCVIVPWDWFWANKZLKZWFWDVRNK
    ZLKZJKZWHVIVLWLVOWNJVIVLWKWDLKWLVIVJWKVKWDLVIWKVJVIWKWAWFNKWAVQJKVJVIWFWAVI
    VQVICAVAVBVCVHUAZVAVBVCVHUBZOZUCZVIEAVDVEVFVGUDZWQOZUEVIWAVQXAWRUFVIECAWTWP
    WQULPQVIWDVKVIDBVDVEVFVGUGZVAVBVCVHUHZUIQRVIWKWDVIWFWAWSXAUJVIVTVIDBXBXCOZU
    CZUMSVIVOWMWFLKWNVIVMWMVNWFLVIWMVMVIWMVRWDNKVRVTJKVMVIWDVRXEVIFBVDVEVFVGUNZ
    XCOZUEVIVRVTXGXDUFVIFDBXFXBXCULPQVIWFVNVICAWPWQUIQRVIWMWFVIWDVRXEXGUJWSUMSR
    VIWDGHZWFGHZIZVRGHZWAGHZIZIWOWHUOVIXJXMVIXHXIXEWSTVIXKXLXGXATTWDWFVRWAUPUQS
    VIWEWIWGWJJVIVTWAXDXAURVIVQVRWRXGURRVIWBVSVIVTWAXDXAUSVIVQVRWRXGUSUTPQ $.


  $( The signed area of a triangle with complex vertices ` A ` , ` B ` , ` C `
     does not depend on the vertex it is computed from: the imaginary part of
     ` ( ( * `` ( B - A ) ) x. ( C - A ) ) ` is invariant under the cyclic
     shift of the vertices.  The products themselves differ in general; only
     their imaginary parts agree.  (Contributed by JAG, 13-Oct-2026.) $)
  lawsinarea $p |- ( ( A e. CC /\ B e. CC /\ C e. CC )
      -> ( Im ` ( ( * ` ( B - A ) ) x. ( C - A ) ) )
      = ( Im ` ( ( * ` ( C - B ) ) x. ( A - B ) ) ) ) $=
    ( cc wcel w3a cmin co ccj cfv cmul cim cre simp2 simp1 subcld simp3 oveq12d
    resubd recnd wa wceq jca imcjmul syl imsubd eqtrd recld 3jca det3cyc eqcomd
    imcld ) ADEBDECDEFBAGHIJCAGHKHLJCBGHMJABGHLJKHCBGHLJABGHMJKHGHCBGHIJABGHKHL
    JADEBDECDEFBAGHIJCAGHKHLJCMJBMJGHALJBLJGHKHCLJBLJGHAMJBMJGHKHGHCBGHMJABGHLJ
    KHCBGHLJABGHMJKHGHADEBDECDEFBAGHIJCAGHKHLJBMJAMJGHCLJALJGHKHBLJALJGHCMJAMJG
    HKHGHCMJBMJGHALJBLJGHKHCLJBLJGHAMJBMJGHKHGHADEBDECDEFBAGHIJCAGHKHLJBAGHMJCA
    GHLJKHBAGHLJCAGHMJKHGHBMJAMJGHCLJALJGHKHBLJALJGHCMJAMJGHKHGHADEBDECDEFBAGHD
    ECAGHDEUABAGHIJCAGHKHLJBAGHMJCAGHLJKHBAGHLJCAGHMJKHGHUBADEBDECDEFBAGHDECAGH
    DEADEBDECDEFBAADEBDECDENADEBDECDEOPADEBDECDEFCAADEBDECDEQADEBDECDEOPUCBAGHC
    AGHUDUEADEBDECDEFBAGHMJCAGHLJKHBMJAMJGHCLJALJGHKHBAGHLJCAGHMJKHBLJALJGHCMJA
    MJGHKHGADEBDECDEFBAGHMJBMJAMJGHCAGHLJCLJALJGHKADEBDECDEFBAADEBDECDENADEBDEC
    DEOSADEBDECDEFCAADEBDECDEQADEBDECDEOUFRADEBDECDEFBAGHLJBLJALJGHCAGHMJCMJAMJ
    GHKADEBDECDEFBAADEBDECDENADEBDECDEOUFADEBDECDEFCAADEBDECDEQADEBDECDEOSRRUGA
    DEBDECDEFAMJDEALJDEBMJDEFBLJDECMJDECLJDEFUABMJAMJGHCLJALJGHKHBLJALJGHCMJAMJ
    GHKHGHCMJBMJGHALJBLJGHKHCLJBLJGHAMJBMJGHKHGHUBADEBDECDEFAMJDEALJDEBMJDEFBLJ
    DECMJDECLJDEFADEBDECDEFAMJDEALJDEBMJDEADEBDECDEFAMJADEBDECDEFAADEBDECDEOUHT
    ADEBDECDEFALJADEBDECDEFAADEBDECDEOULTADEBDECDEFBMJADEBDECDEFBADEBDECDENUHTU
    IADEBDECDEFBLJDECMJDECLJDEADEBDECDEFBLJADEBDECDEFBADEBDECDENULTADEBDECDEFCM
    JADEBDECDEFCADEBDECDEQUHTADEBDECDEFCLJADEBDECDEFCADEBDECDEQULTUIUCAMJALJBMJ
    BLJCMJCLJUJUEUGADEBDECDEFCBGHMJABGHLJKHCBGHLJABGHMJKHGHCMJBMJGHALJBLJGHKHCL
    JBLJGHAMJBMJGHKHGHADEBDECDEFCBGHMJABGHLJKHCMJBMJGHALJBLJGHKHCBGHLJABGHMJKHC
    LJBLJGHAMJBMJGHKHGADEBDECDEFCBGHMJCMJBMJGHABGHLJALJBLJGHKADEBDECDEFCBADEBDE
    CDEQADEBDECDENSADEBDECDEFABADEBDECDEOADEBDECDENUFRADEBDECDEFCBGHLJCLJBLJGHA
    BGHMJAMJBMJGHKADEBDECDEFCBADEBDECDEQADEBDECDENUFADEBDECDEFABADEBDECDEOADEBD
    ECDENSRRUKUGADEBDECDEFCBGHIJABGHKHLJCBGHMJABGHLJKHCBGHLJABGHMJKHGHADEBDECDE
    FCBGHDEABGHDEUACBGHIJABGHKHLJCBGHMJABGHLJKHCBGHLJABGHMJKHGHUBADEBDECDEFCBGH
    DEABGHDEADEBDECDEFCBADEBDECDEQADEBDECDENPADEBDECDEFABADEBDECDEOADEBDECDENPU
    CCBGHABGHUDUEUKUG $.


  ${
    cnrflinv.a $e |- ( ph -> A e. CC ) $.
    cnrflinv.w $e |- ( ph -> W e. CC ) $.
    cnrflinv.z $e |- ( ph -> Z e. CC ) $.
    cnrflinv.n $e |- ( ph -> W =/= A ) $.
    cnrflinv.e $e |- E = ( ( W - A ) / ( * ` ( W - A ) ) ) $.
    $( The reflection of the complex plane across the line through distinct
       points ` A ` and ` W ` maps ` Z ` to
       ` ( A + ( E x. ( * `` ( Z - A ) ) ) ) ` , where ` E ` is the number
       ` ( ( W - A ) / ( * `` ( W - A ) ) ) ` of absolute value ` 1 ` .  This
       theorem shows that the reflection is an involution: applying it twice
       returns ` Z ` .  (Contributed by JAG, 13-Oct-2026.) $)
    cnrflinv $p |- ( ph
        -> ( A + ( E x. ( * ` ( ( A + ( E x. ( * ` ( Z - A ) ) ) ) - A ) ) ) )
        = Z ) $=
      ( cmin co ccj cfv cmul caddc c1 cdiv oveq2d eqtrd wceq a1i subcld subne0d
      cc cjcld cjne0d divcld eqeltrd mulcld pncan2d fveq2d cjmuld cjcjd mulassd
      3eqtrd eqcomd cjdivd oveq12d divmuldivd mulcomd mulne0d mullidd pncan3d
      dividd oveq1d ) ABCBCEBKLZMNZOLZPLBKLZMNZOLZPLBVGPLEAVLVGBPAVLQVGOLZVGAVL
      CCMNZVGOLZOLZCVNOLZVGOLZVMAVKVOCOAVKVIMNVNVHMNZOLVOAVJVIMABVIFACVHACDBKLZ
      VTMNZRLZUECWBUAAJUBZAVTWAADBGFUCZAVTWDUFZAVTWDADBGFIUDZUGZUHUIZAVGAEBHFUC
      ZUFZUJUKULACVHWHWJUMAVSVGVNOAVGWIUNSUPSAVRVPACVNVGWHACWHUFWIUOUQAVQQVGOAV
      QVTWAOLZWKRLZQAVQWBWAVTRLZOLWKWAVTOLZRLWLACWBVNWMOWCAVNWBMNZWMACWBMWCULAW
      OWAWAMNZRLWMAVTWAWDWEWGURAWPVTWARAVTWDUNSTTUSAVTWAWAVTWDWEWEWDWGWFUTAWNWK
      WKRAWAVTWEWDVASUPAWKAVTWAWDWEUJAVTWAWDWEWFWGVBVETVFUPAVGWIVCTSABEFHVDT $.
  $}


  ${
    cnrflfix.a $e |- ( ph -> A e. CC ) $.
    cnrflfix.w $e |- ( ph -> W e. CC ) $.
    cnrflfix.n $e |- ( ph -> W =/= A ) $.
    cnrflfix.e $e |- E = ( ( W - A ) / ( * ` ( W - A ) ) ) $.
    $( The reflection across the line through distinct points ` A ` and ` W `
       (see ~ cnrflinv ) fixes both ` A ` and ` W ` .  (Contributed by JAG,
       13-Oct-2026.) $)
    cnrflfix $p |- ( ph
        -> ( ( A + ( E x. ( * ` ( A - A ) ) ) ) = A
        /\ ( A + ( E x. ( * ` ( W - A ) ) ) ) = W ) ) $=
      ( cmin co ccj cfv cmul caddc wceq cc0 subidd a1i eqtrd oveq2d fveq2d cdiv
      cj0 cc subcld cjcld subne0d cjne0d divcld eqeltrd mul01d addridd divcan1d
      oveq1d pncan3d jca ) ABCBBIJZKLZMJZNJZBOBCDBIJZKLZMJZNJZDOAUTBPNJBAUSPBNA
      USCPMJPAURPCMAURPKLZPAUQPKABEQUAVEPOAUCRSTACACVAVBUBJZUDCVFOAHRZAVAVBADBF
      EUEZAVAVHUFZAVAVHADBFEGUGUHZUIUJUKSTABEULSAVDBVANJDAVCVABNAVCVFVBMJVAACVF
      VBMVGUNAVAVBVHVIVJUMSTABDEFUOSUP $.
  $}


  ${
    cnrflsw.a $e |- ( ph -> A e. CC ) $.
    cnrflsw.b $e |- ( ph -> B e. CC ) $.
    cnrflsw.z $e |- ( ph -> Z e. CC ) $.
    cnrflsw.n $e |- ( ph -> B =/= A ) $.
    cnrflsw.d $e |- D = ( ( B - A ) / ( * ` ( B - A ) ) ) $.
    cnrflsw.e $e |- E = ( ( A - B ) / ( * ` ( A - B ) ) ) $.
    $( The reflection across the line through distinct points ` A ` and ` B `
       (see ~ cnrflinv ) takes the same value at every point ` Z ` whether it
       is written from ` A ` or from ` B ` .  (Contributed by JAG,
       13-Oct-2026.) $)
    cnrflsw $p |- ( ph -> ( B + ( E x. ( * ` ( Z - B ) ) ) )
        = ( A + ( D x. ( * ` ( Z - A ) ) ) ) ) $=
      ( cmin co ccj cfv cmul caddc eqcomd eqtrd cdiv cneg a1i negsubdi2d fveq2d
      subcld cjnegd oveq12d cjcld subne0d cjne0d div2negd 3eqtrd oveq1d npncand
      wceq oveq2d cjaddd cc divcld eqeltrd adddid mulcld addassd add32d pncan3d
      divcan1d ) ACEFCMNZOPZQNZRNCDVIQNZRNZBDFBMNZOPZQNZRNZAVJVKCRAEDVIQAECBMNZ
      VQOPZUANZDAEBCMNZVTOPZUANZVQUBZVRUBZUANVSEWBUPALUCAVTWCWAWDUAAWCVTACBHGUD
      SZAWAWCOPWDAVTWCOWEUEAVQACBHGUFZUGTUHAVQVRWFAVQWFUIZAVQWFACBHGJUJUKZULUMA
      DVSDVSUPAKUCZSTUNUQAVPVLAVPBVQRNZVKRNZVLAVPBVKVQRNZRNZBVKRNVQRNZWKAVOWLBR
      AVODVIVRRNZQNVKDVRQNZRNWLAVNWODQAVNVHVQRNZOPWOAVMWQOAWQVMAFCBIHGUOSUEAVHV
      QAFCIHUFZWFURTUQADVIVRADVSUSWIAVQVRWFWGWHUTVAZAVHWRUIZWGVBAWPVQVKRAWPVSVR
      QNVQADVSVRQWIUNAVQVRWFWGWHVGTUQUMUQAWNWMABVKVQGADVIWSWTVCZWFVDSABVKVQGXAW
      FVEUMAWJCVKRABCGHVFUNTST $.
  $}


  ${
    $d A x y $.  $d B x y $.
    ang2exp.1 $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    ang2exp.a $e |- ( ph -> A e. CC ) $.
    ang2exp.an $e |- ( ph -> A =/= 0 ) $.
    ang2exp.b $e |- ( ph -> B e. CC ) $.
    ang2exp.bn $e |- ( ph -> B =/= 0 ) $.
    $( The rotation by twice the signed angle from a nonzero complex number
       ` A ` to a nonzero ` B ` has coefficient
       ` ( ( B / A ) / ( * `` ( B / A ) ) ) ` , a rational expression in ` A `
       and ` B ` .  Here ` F ` is the signed angle function
` ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im `` ( log `` ( y / x ) )
) ) ` ,
       so that ` ( A F B ) ` is the angle from ` A ` to ` B ` .  (Contributed
       by JAG,
       13-Oct-2026.) $)
    ang2exp $p |- ( ph -> ( exp ` ( _i x. ( 2 x. ( A F B ) ) ) )
        = ( ( B / A ) / ( * ` ( B / A ) ) ) ) $=
      ( ci c2 co cmul ce cfv cdiv cexp wcel ccj cabs clog angvald oveq2d fveq2d
      cim cc ax-icn a1i divcld divne0d logcld imcld recnd mul12d cz wceq mulcld
      2cn 2z efexp syl2anc 3eqtrd cc0 wne efiarg oveq1d abscld sqdivd absvalsqd
      absne0d sqvald cjcld cjne0d divcan5d eqtrd ) ALMDEFNZONZONZPQZEDRNZWBONZW
      BWBUAQZONZRNZWBWDRNAWAWBMSNZWBUBQZMSNZRNZWCWIRNWFAWALWBUCQZUGQZONZPQZMSNZ
      WBWHRNZMSNWJAWALMWLONZONZPQMWMONZPQZWOAVTWRPAVSWQLOAVRWLMOABCFDEGHIJKUDUE
      UEUFAWRWSPALMWLLUHTAUIUJZMUHTAUTUJAWLAWKAWBAEDJHIUKZAEDJHKIULZUMUNUOZUPUF
      AWMUHTMUQTZWTWOURALWLXAXDUSXEAVAUJWMMVBVCVDAWNWPMSAWBUHTWBVEVFWNWPURXBXCW
      BVGVCVHAWBWHXBAWHAWBXBVIUOAWBXBXCVLVJVDAWGWCWIRAWBXBVMVHAWIWEWCRAWBXBVKUE
      VDAWBWDWBXBAWBXBVNXBAWBXBXCVOXCVPVQ $.
  $}


  ${
    $d A x y $.  $d B x y $.  $d C x y $.
    cnrfl2.1 $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    cnrfl2.a $e |- ( ph -> A e. CC ) $.
    cnrfl2.b $e |- ( ph -> B e. CC ) $.
    cnrfl2.c $e |- ( ph -> C e. CC ) $.
    cnrfl2.z $e |- ( ph -> Z e. CC ) $.
    cnrfl2.bn $e |- ( ph -> B =/= A ) $.
    cnrfl2.cn $e |- ( ph -> C =/= A ) $.
    cnrfl2.d $e |- D = ( ( B - A ) / ( * ` ( B - A ) ) ) $.
    cnrfl2.e $e |- E = ( ( C - A ) / ( * ` ( C - A ) ) ) $.
    $( The reflection across the line through ` A ` and ` B ` followed by the
       reflection across the line through ` A ` and ` C ` is the rotation about
       ` A ` by twice the signed angle from ` ( B - A ) ` to ` ( C - A ) ` .
       ` F ` is the signed angle function, as in ~ ang2exp .  (Contributed by
       JAG, 13-Oct-2026.) $)
    cnrfl2 $p |- ( ph
        -> ( A + ( E x. ( * ` ( ( A + ( D x. ( * ` ( Z - A ) ) ) ) - A ) ) ) )
        = ( A
        + ( ( exp ` ( _i x. ( 2 x. ( ( B - A ) F ( C - A ) ) ) ) )
        x. ( Z - A ) ) ) ) $=
      ( co cmin ccj cfv cmul caddc ci c2 ce cdiv wceq a1i subcld subne0d cjne0d
      cc cjcld divcld eqeltrd mulcld pncan2d fveq2d cjmuld cjcjd oveq2d mulassd
      3eqtrd eqcomd cjdivd oveq12d divmuldivd mulcomd ang2exp divdivdivd oveq1d
      eqtrd ) AHDGJDUATZUBUCZUDTZUETDUATZUBUCZUDTZUFUGEDUATZFDUATZITUDTUDTUHUCZ
      VPUDTZDUEAWAHGUBUCZUDTZVPUDTZWEAWAHWFVPUDTZUDTZWHAVTWIHUDAVTVRUBUCWFVQUBU
      CZUDTWIAVSVRUBADVRLAGVQAGWBWBUBUCZUITZUOGWMUJARUKZAWBWLAEDMLULZAWBWOUPZAW
      BWOAEDMLPUMZUNZUQURZAVPAJDOLULZUPZUSUTVAAGVQWSXAVBAWKVPWFUDAVPWTVCVDVFVDA
      WHWJAHWFVPAHWCWCUBUCZUITZUOHXCUJASUKZAWCXBAFDNLULZAWCXEUPZAWCXEAFDNLQUMZU
      NZUQURAGWSUPWTVEVGVOAWGWDVPUDAWGWCWLUDTZWBXBUDTZUITZWDAWGXCWLWBUITZUDTXIX
      BWBUDTZUITXKAHXCWFXLUDXDAWFWMUBUCWLWLUBUCZUITXLAGWMUBWNVAAWBWLWOWPWRVHAXN
      WBWLUIAWBWOVCVDVFVIAWCXBWLWBXEXFWPWOXHWQVJAXMXJXIUIAXBWBXFWOVKVDVFAWDXKAW
      DWCWBUITZXOUBUCZUITXOXBWLUITZUITXKABCWBWCIKWOWQXEXGVLAXPXQXOUIAWCWBXEWOWQ
      VHVDAWCWBXBWLXEWOXFWPWQWRXHVMVFVGVOVNVOVD $.
  $}


  ${
    $d A x y $.  $d B x y $.
    angioo.1 $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    angioo.a $e |- ( ph -> A e. CC ) $.
    angioo.an $e |- ( ph -> A =/= 0 ) $.
    angioo.b $e |- ( ph -> B e. CC ) $.
    angioo.bn $e |- ( ph -> B =/= 0 ) $.
    $( The signed angle from a nonzero complex number ` A ` to a nonzero ` B `
       lies in the open interval ` ( 0 (,) _pi ) ` exactly when the imaginary
       part of ` ( B / A ) ` is positive. ` F ` is the signed angle function,
       as in ~ ang2exp .  (Contributed by JAG, 13-Oct-2026.) $)
    angioo $p |- ( ph
        -> ( ( A F B ) e. ( 0 (,) _pi ) <-> 0 < ( Im ` ( B / A ) ) ) ) $=
      ( co cc0 wcel cdiv cfv cim clt wbr adantr cpi cioo clog angvald eleq1d wa
      cabs csin simpr sinq12gt0 syl cc wne divcld divne0d sinarg syl2anc abscld
      wceq cr absne0d imdivd eqtrd breqtrd wb crp absrpcl rpgt0d gt0div syl3anc
      imcld mpbird ex wi argimgt0 impbid bitrd ) ADEFLZMUAUBLZNEDOLZUCPQPZVSNZM
      VTQPZRSZAVRWAVSABCFDEGHIJKUDUEAWBWDAWBWDAWBUFZWDMWCVTUGPZOLZRSZWEMWAUHPZW
      GRWEWBMWIRSAWBUIWAUJUKWEWIVTWFOLQPZWGWEVTULNZVTMUMZWIWJUSAWKWBAEDJHIUNZTZ
      AWLWBAEDJHKIUOZTVTUPUQWEWFVTAWFUTNZWBAVTWMURTZWNAWFMUMWBAVTWMWOVATVBVCVDW
      EWCUTNZWPMWFRSZWDWHVEAWRWBAVTWMVKTWQAWSWBAWFAWKWLWFVFNWMWOVTVGUQVHTWCWFVI
      VJVLVMAWKWDWBVNWMWKWDWBVTVOVMUKVPVQ $.
  $}


  ${
    $d A x y $.  $d B x y $.  $d C x y $.
    ang180pos.1 $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    ang180pos.a $e |- ( ph -> A e. CC ) $.
    ang180pos.b $e |- ( ph -> B e. CC ) $.
    ang180pos.c $e |- ( ph -> C e. CC ) $.
    ang180pos.ab $e |- ( ph -> A =/= B ) $.
    ang180pos.bc $e |- ( ph -> B =/= C ) $.
    ang180pos.ca $e |- ( ph -> C =/= A ) $.
    ang180pos.o $e |- ( ph -> ( ( B - A ) F ( C - A ) ) e. ( 0 (,) _pi ) ) $.
    $( If the angle at ` A ` of the triangle with vertices ` A ` , ` B ` ,
       ` C ` , measured from ` ( B - A ) ` to ` ( C - A ) ` , lies in
       ` ( 0 (,) _pi ) ` , so that the triangle is positively oriented, then so
       do its angles at ` B ` and at ` C ` taken in the same cyclic order, and
       the three angles sum to ` _pi ` . ` F ` is the signed angle function, as
       in ~ ang2exp .  (Contributed by JAG, 13-Oct-2026.) $)
    ang180pos $p |- ( ph
        -> ( ( ( C - B ) F ( A - B ) ) e. ( 0 (,) _pi )
        /\ ( ( A - C ) F ( B - C ) ) e. ( 0 (,) _pi )
        /\ ( ( ( ( C - B ) F ( A - B ) ) + ( ( A - C ) F ( B - C ) ) )
        + ( ( B - A ) F ( C - A ) ) ) = _pi ) ) $=
      ( co cc0 wcel clt wbr cmin cpi cioo caddc wceq cdiv cim cfv ccj cmul cabs
      c2 cexp subcld necomd subne0d angioo mpbid cc wne jca imdivcjabs2 syl2anc
      wa breqtrd cr wb cjcld mulcld imcld abscld resqcld absne0d sqgt0d syl3anc
      gt0div mpbird lawsinarea breqtrrd cneg wo cpr w3a 3jca ang180 elpri wn wi
      syl pire renegcl ax-mp a1i 0re elioore readdcld pipos lt0neg2 mpbi simpld
      eliooord addgt0d lttrd ltned neneqd orel1 mpd ) AFEUAPZDEUAPZGPZQUBUCPZRZ
      DFUAPZEFUAPZGPZXKRZXJXOUDPZEDUAPZFDUAPZGPZUDPZUBUEZAXLQXIXHUFPUGUHZSTAQXH
      UIUHZXIUJPZUGUHZXHUKUHZULUMPZUFPZYCSAQYFSTZQYISTZAQXRUIUHZXSUJPZUGUHZYFSA
      QYNSTZQYNXRUKUHZULUMPZUFPZSTZAQXSXRUFPUGUHZYRSAXTXKRZQYTSTOABCXRXSGHAEDJI
      UNZAEDJIADELUOUPZAFDKIUNZAFDKINUPUQURAXRUSRZXRQUTZVDXSUSRYTYRUEAUUEUUFUUB
      UUCVAUUDXRXSVBVCVEAYNVFRYQVFRQYQSTYOYSVGAYMAYLXSAXRUUBVHUUDVIVJAYPAXRUUBV
      KZVLAYPUUGAXRUUBUUCVMVNYNYQVPVOVQADUSRZEUSRZFUSRZYNYFUEIJKDEFVRVOVEZAYFVF
      RYHVFRQYHSTYJYKVGAYEAYDXIAXHAFEKJUNZVHADEIJUNZVIVJAYGAXHUULVKZVLAYGUUNAXH
      UULAFEKJAEFMUOUPZVMVNYFYHVPVOURAXHUSRZXHQUTZVDXIUSRYCYIUEAUUPUUQUULUUOVAU
      UMXHXIVBVCVSABCXHXIGHUULUUOUUMADEIJLUPUQVQZAXPQXNXMUFPUGUHZSTAQXMUIUHZXNU
      JPZUGUHZXMUKUHZULUMPZUFPZUUSSAQUVBSTZQUVESTZAQYFUVBSUUKAUUIUUJUUHYFUVBUEJ
      KIEFDVRVOVEAUVBVFRUVDVFRQUVDSTUVFUVGVGAUVAAUUTXNAXMADFIKUNZVHAEFJKUNZVIVJ
      AUVCAXMUVHVKZVLAUVCUVJAXMUVHADFIKAFDNUOZUPZVMVNUVBUVDVPVOURAXMUSRZXMQUTZV
      DXNUSRUUSUVEUEAUVMUVNUVHUVLVAUVIXMXNVBVCVSABCXMXNGHUVHUVLUVIAEFJKMUPUQVQZ
      AYAUBVTZUEZYBWAZYBAYAUVPUBWBRZUVRAUUHUUIUUJWCDEUTZEFUTZDFUTZWCUVSAUUHUUIU
      UJIJKWDAUVTUWAUWBLMUVKWDBCDEFGHWEVCYAUVPUBWFWIAUVQWGUVRYBWHAYAUVPAUVPYAAU
      VPYAUVPVFRZAUBVFRZUWCWJUBWKWLWMZAUVPQYAUWEQVFRAWNWMAXQXTAXJXOAXLXJVFRUURX
      JQUBWOWIZAXPXOVFRUVOXOQUBWOWIZWPZAUUAXTVFROXTQUBWOWIZWPUVPQSTZAQUBSTZUWJW
      QUWDUWKUWJVGWJUBWRWLWSWMAXQXTUWHUWIAXJXOUWFUWGAQXJSTZXJUBSTZAXLUWLUWMVDUU
      RXJQUBXAWIWTAQXOSTZXOUBSTZAXPUWNUWOVDUVOXOQUBXAWIWTXBAQXTSTZXTUBSTZAUUAUW
      PUWQVDOXTQUBXAWIWTXBXCXDUOXEUVQYBXFWIXGWD $.
  $}


  ${
    $d A x y $.  $d B x y $.  $d R x y $.
    morlemfix.f $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    morlemfix.a $e |- ( ph -> A e. CC ) $.
    morlemfix.b $e |- ( ph -> B e. CC ) $.
    morlemfix.r $e |- ( ph -> R e. CC ) $.
    morlemfix.ba $e |- ( ph -> B =/= A ) $.
    morlemfix.ra $e |- ( ph -> R =/= A ) $.
    morlemfix.rb $e |- ( ph -> R =/= B ) $.
    morlemfix.1 $e |- ( ph -> ( ( B - A ) F ( R - A ) ) = X ) $.
    morlemfix.2 $e |- ( ph -> ( ( R - B ) F ( A - B ) ) = Y ) $.
    $( Let ` X ` be the signed angle at ` A ` from ` ( B - A ) ` to
       ` ( R - A ) ` , and ` Y ` the signed angle at ` B ` from ` ( R - B ) `
       to ` ( A - B ) ` .  Then the rotation about ` B ` by ` ( 2 x. Y ) `
       followed by the rotation about ` A ` by ` ( 2 x. X ) ` fixes ` R ` :
       each rotation is the composite of two reflections ( ~ cnrfl2 ), and the
       reflections across the line through ` A ` and ` B ` cancel.
       (Contributed by JAG, 13-Oct-2026.) $)
    morlemfix $p |- ( ph
        -> ( A
        + ( ( exp ` ( _i x. ( 2 x. X ) ) )
        x. ( ( B + ( ( exp ` ( _i x. ( 2 x. Y ) ) ) x. ( R - B ) ) ) - A ) ) )
        = R ) $=
      ( cmul co ci c2 ce cfv cmin caddc ccj cdiv oveq2d fveq2d wceq eqid simprd
      cnrflfix oveq1d eqcomd necomd cnrfl2 oveq12d subcld subne0d cjne0d divcld
      eqtrd cjcld mulcld addcld cnrflsw cnrflinv ) ADUAUBHSTZSTZUCUDZEUAUBISTZS
      TZUCUDZFEUETZSTZUFTZDUETZSTZUFTZDUAUBEDUETZFDUETZGTZSTZSTZUCUDZEDEUETZWHU
      GUDZUHTZVPUGUDZSTZUFTZDUETZSTZUFTZFAWPWAAWOVTDUFAWGVLWNVSSAWFVKUCAWEVJUAS
      AWDHUBSQUIUIUJAWMVRDUEAWMEUAUBVPWHGTZSTZSTZUCUDZVPSTZUFTZVRAWMEWJEVPWKUHT
      ZWKSTUFTZEUETZUGUDZSTZUFTZXBAXHWMAXGWLEUFAXFWKWJSAXEVPUGAXDFEUEAEXCEEUETU
      GUDSTUFTEUKXDFUKAEXCFLMPXCULZUNUMUOUJUIUIUPABCEFDXCWJGFJLMKMPAEDNUQZXIWJU
      LZURVDAXAVQEUFAWTVOVPSAWSVNUCAWRVMUASAWQIUBSRUIUIUJUOUIVDUOUSUIUPAWPDWCWC
      UGUDZUHTZDWBWBUGUDUHTZWNUGUDZSTZUFTZDUETZUGUDZSTZUFTZFAYAWPABCDEFXNXMGWMJ
      KLMAEWLLAWJWKAWHWIADEKLUTZAWHYBVEAWHYBADEKLXJVAVBVCAVPAFEMLUTVEVFVGNOXNUL
      ZXMULZURUPAYADXMXLSTZUFTZFAXTYEDUFAXSXLXMSAXRWCUGAXQFDUEAXQDXNDXNXLSTUFTZ
      DUETZUGUDZSTZUFTFAXPYJDUFAXOYIXNSAWNYHUGAWMYGDUEADEXNWJFKLMNYCXKVHUOUJUIU
      IADXNEFKLMNYCVIVDUOUJUIUIADXMDDUETUGUDSTUFTDUKYFFUKADXMFKMOYDUNUMVDVDVD
      $.
  $}


  ${
    $d A x y $.  $d B x y $.  $d C x y $.  $d P x y $.  $d Q x y $.
    $d R x y $.
    morlemfix3.f $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    morlemfix3.a $e |- ( ph -> A e. CC ) $.
    morlemfix3.b $e |- ( ph -> B e. CC ) $.
    morlemfix3.c $e |- ( ph -> C e. CC ) $.
    morlemfix3.p $e |- ( ph -> P e. CC ) $.
    morlemfix3.q $e |- ( ph -> Q e. CC ) $.
    morlemfix3.r $e |- ( ph -> R e. CC ) $.
    morlemfix3.ab $e |- ( ph -> A =/= B ) $.
    morlemfix3.bc $e |- ( ph -> B =/= C ) $.
    morlemfix3.ca $e |- ( ph -> C =/= A ) $.
    morlemfix3.ra $e |- ( ph -> R =/= A ) $.
    morlemfix3.rb $e |- ( ph -> R =/= B ) $.
    morlemfix3.pb $e |- ( ph -> P =/= B ) $.
    morlemfix3.pc $e |- ( ph -> P =/= C ) $.
    morlemfix3.qc $e |- ( ph -> Q =/= C ) $.
    morlemfix3.qa $e |- ( ph -> Q =/= A ) $.
    morlemfix3.1 $e |- ( ph -> ( ( B - A ) F ( R - A ) ) = X ) $.
    morlemfix3.2 $e |- ( ph -> ( ( Q - A ) F ( C - A ) ) = X ) $.
    morlemfix3.3 $e |- ( ph -> ( ( C - B ) F ( P - B ) ) = Y ) $.
    morlemfix3.4 $e |- ( ph -> ( ( R - B ) F ( A - B ) ) = Y ) $.
    morlemfix3.5 $e |- ( ph -> ( ( A - C ) F ( Q - C ) ) = Z ) $.
    morlemfix3.6 $e |- ( ph -> ( ( P - C ) F ( B - C ) ) = Z ) $.
    $( The fixed-point equations of ~ morlemfix at all three sides of the
       triangle with vertices ` A ` , ` B ` , ` C ` .  The lines from ` A ` to
       ` R ` and to ` Q ` make the equal angles ` X ` with the sides at ` A ` ;
       likewise ` Y ` at ` B ` for ` P ` and ` R ` , and ` Z ` at ` C ` for
       ` Q ` and ` P ` .  The rotations about consecutive vertices by twice
       these angles compose to maps fixing ` R ` , ` P ` and ` Q `
       respectively.  (Contributed by JAG, 13-Oct-2026.) $)
    morlemfix3 $p |- ( ph
        -> ( ( A
        + ( ( exp ` ( _i x. ( 2 x. X ) ) )
        x. ( ( B + ( ( exp ` ( _i x. ( 2 x. Y ) ) ) x. ( R - B ) ) ) - A ) ) )
        = R
        /\ ( B
        + ( ( exp ` ( _i x. ( 2 x. Y ) ) )
        x. ( ( C + ( ( exp ` ( _i x. ( 2 x. Z ) ) ) x. ( P - C ) ) ) - B ) ) )
        = P
        /\ ( C
        + ( ( exp ` ( _i x. ( 2 x. Z ) ) )
        x. ( ( A + ( ( exp ` ( _i x. ( 2 x. X ) ) ) x. ( Q - A ) ) ) - C ) ) )
        = Q ) ) $=
      ( ci c2 cmul co ce cfv cmin caddc wceq necomd morlemfix 3jca ) ADUPUQKURU
      SURUSUTVAZEUPUQLURUSURUSUTVAZIEVBUSURUSVCUSDVBUSURUSVCUSIVDEVIFUPUQMURUSU
      RUSUTVAZGFVBUSURUSVCUSEVBUSURUSVCUSGVDFVJDVHHDVBUSURUSVCUSFVBUSURUSVCUSHV
      DABCDEIJKLNOPTADEUAVEUDUEUJUMVFABCEFGJLMNPQRAEFUBVEUFUGULUOVFABCFDHJMKNQO
      SAFDUCVEUHUIUNUKVFVG $.
  $}


  ${
    $d A x y $.  $d B x y $.
    morlemcub.f $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    morlemcub.a $e |- ( ph -> A e. CC ) $.
    morlemcub.an $e |- ( ph -> A =/= 0 ) $.
    morlemcub.b $e |- ( ph -> B e. CC ) $.
    morlemcub.bn $e |- ( ph -> B =/= 0 ) $.
    morlemcub.x $e |- X = ( ( A F B ) / 3 ) $.
    $( If ` X ` is one third of the signed angle ` ( A F B ) ` , the cube of
       the rotation coefficient ` ( exp `` ( _i x. ( 2 x. X ) ) ) ` is the
       rotation coefficient for twice the whole angle. ` F ` is the signed
       angle function, as in ~ ang2exp .  (Contributed by JAG, 13-Oct-2026.) $)
    morlemcub $p |- ( ph -> ( ( exp ` ( _i x. ( 2 x. X ) ) ) ^ 3 )
        = ( exp ` ( _i x. ( 2 x. ( A F B ) ) ) ) ) $=
      ( ci c2 cmul co c3 cc a1i cfv cexp wcel wceq ax-icn 2cn cdiv clog angvald
      ce cz cim divcld divne0d logcld imcld recnd eqeltrd 3cn cc0 wne mulcld 3z
      3ne0 efexp syl2anc eqcomd mul12d oveq2d divcan2d eqtrd fveq2d ) ANOGPQZPQ
      ZUJUARUBQZRVNPQZUJUAZNODEFQZPQZPQZUJUAAVQVOAVNSUCRUKUCZVQVOUDANVMNSUCAUET
      ZAOGOSUCAUFTZAGVRRUGQZSGWDUDAMTZAVRRAVREDUGQZUHUAZULUAZSABCFDEHIJKLUIAWHA
      WGAWFAEDKIJUMAEDKILJUNUOUPUQURZRSUCAUSTZRUTVAAVDTZUMURZVBZVBWAAVCTVNRVEVF
      VGAVPVTUJAVPNRVMPQZPQVTARNVMWJWBWMVHAWNVSNPAWNORGPQZPQVSAROGWJWCWLVHAWOVR
      OPAWORWDPQVRAGWDRPWEVIAVRRWIWJWKVJVKVIVKVIVKVLVK $.
  $}


  ${
    $d A x y $.  $d B x y $.  $d C x y $.
    morlemid.f $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    morlemid.x $e |- X = ( ( ( B - A ) F ( C - A ) ) / 3 ) $.
    morlemid.y $e |- Y = ( ( ( C - B ) F ( A - B ) ) / 3 ) $.
    morlemid.z $e |- Z = ( ( ( A - C ) F ( B - C ) ) / 3 ) $.
    morlemid.a $e |- ( ph -> A e. CC ) $.
    morlemid.b $e |- ( ph -> B e. CC ) $.
    morlemid.c $e |- ( ph -> C e. CC ) $.
    morlemid.w $e |- ( ph -> W e. CC ) $.
    morlemid.ab $e |- ( ph -> A =/= B ) $.
    morlemid.bc $e |- ( ph -> B =/= C ) $.
    morlemid.ca $e |- ( ph -> C =/= A ) $.
    $( Let ` X ` , ` Y ` , ` Z ` be one third of the angles of the triangle
       with vertices ` A ` , ` B ` , ` C ` .  The rotations about ` C ` , ` B `
       and ` A ` by six times these angles, applied in that order, compose to
       the identity: by ~ cnrfl2 each is the composite of two reflections in
       sides of the triangle, and the reflections cancel in pairs.
       (Contributed by JAG, 13-Oct-2026.) $)
    morlemid $p |- ( ph
        -> ( A
        + ( ( ( exp ` ( _i x. ( 2 x. X ) ) ) ^ 3 )
        x. ( ( B
        + ( ( ( exp ` ( _i x. ( 2 x. Y ) ) ) ^ 3 )
        x. ( ( C + ( ( ( exp ` ( _i x. ( 2 x. Z ) ) ) ^ 3 ) x. ( W - C ) ) )
        - B ) ) ) - A ) ) ) = W ) $=
      ( ci c2 cmul co ce cfv c3 cexp cmin caddc subcld necomd subne0d morlemcub
      oveq1d oveq2d oveq12d ccj cdiv cc cjcld cjne0d divcld mulcld eqid cnrflsw
      addcld cnrfl2 eqtrd eqcomd fveq2d cnrflinv eqeltrrd ) ADUCUDIUEUFUEUFUGUH
      UIUJUFZEUCUDJUEUFUEUFUGUHUIUJUFZFUCUDKUEUFUEUFUGUHUIUJUFZHFUKUFZUEUFZULUF
      ZEUKUFZUEUFZULUFZDUKUFZUEUFZULUFDUCUDEDUKUFZFDUKUFZGUFUEUFUEUFUGUHZEUCUDF
      EUKUFZDEUKUFZGUFUEUFUEUFUGUHZFUCUDDFUKUFZEFUKUFZGUFUEUFUEUFUGUHZVSUEUFZUL
      UFZEUKUFZUEUFZULUFZDUKUFZUEUFZULUFZHAWFXBDULAVPWIWEXAUEABCWGWHGILAEDQPUMA
      EDQPADETUNZUOAFDRPUMAFDRPUBUOMUPAWDWTDUKAWCWSEULAVQWLWBWRUEABCWJWKGJLAFER
      QUMAFERQAEFUAUNZUOADEPQUMZADEPQTUOZNUPAWAWQEUKAVTWPFULAVRWOVSUEABCWMWNGKL
      ADFPRUMZADFPRAFDUBUNZUOZAEFQRUMZAEFQRUAUOZOUPUQURUQUSURUQUSURAXCDWHWHUTUH
      VAUFZDWGWGUTUHVAUFZXAUTUHZUEUFZULUFZDUKUFZUTUHZUEUFZULUFZHAYAXCABCDEFXNXM
      GWTLPQRAEWKWKUTUHZVAUFZFWMWMUTUHZVAUFZVSUTUHZUEUFZULUFZEUKUFZUTUHZUEUFZUL
      UFZWTVBAYLEYCEWJWJUTUHVAUFZWRUTUHZUEUFZULUFZEUKUFZUTUHZUEUFZULUFZWTAYTYLA
      YSYKEULAYRYJYCUEAYQYIUTAYPYHEUKAYPEYMEYMYJUEUFULUFZEUKUFZUTUHZUEUFZULUFYH
      AYOUUDEULAYNUUCYMUEAWRUUBUTAWQUUAEUKAUUAWQAUUAFWNWNUTUHZVAUFZYHFUKUFZUTUH
      ZUEUFZULUFZWQAFEUUFYMYHRQAFYGRAYEYFAWMYDXHAWMXHVCAWMXHXJVDVEAVSAHFSRUMVCV
      FVIZUAUUFVGZYMVGZVHABCFDEYEUUFGHLRPQSXIUAYEVGZUULVJZVKVLUQVMURURAEYMFYHQR
      UUKXEUUMVNVKUQVMURURVLABCEFDYMYCGWQLQRPAUUJWQVBUUOAFUUIRAUUFUUHAWNUUEXKAW
      NXKVCAWNXKXLVDVEAUUGAYHFUUKRUMVCVFVIVOXETUUMYCVGZVJVKZAEYKQAYCYJAWKYBXFAW
      KXFVCAWKXFXGVDVEAYIAYHEUUKQUMVCVFVIVOXDUBXNVGZXMVGZVJVLAYADXMYHDUKUFZUTUH
      ZUEUFZULUFZHAXTUVBDULAXSUVAXMUEAXRUUTUTAXQYHDUKAXQDXNDXNUVAUEUFULUFZDUKUF
      ZUTUHZUEUFZULUFZYHAUVHXQAUVGXPDULAUVFXOXNUEAUVEXAUTAUVDWTDUKAUVDYLWTAYLUV
      DADEXNYCYHPQUUKXDUURUUPVHVLUUQVKUQVMURURVLADXNEYHPQUUKXDUURVNVKUQVMURURAU
      VCDXMDXMHDUKUFUTUHUEUFULUFZDUKUFZUTUHZUEUFZULUFHAUVBUVLDULAUVAUVKXMUEAUUT
      UVJUTAYHUVIDUKADFXMYEHPRSUBUUSUUNVHUQVMURURADXMFHPRSUBUUSVNVKVKVKVK $.
  $}


  ${
    $d A x y $.  $d B x y $.  $d C x y $.
    morlemj.f $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    morlemj.x $e |- X = ( ( ( B - A ) F ( C - A ) ) / 3 ) $.
    morlemj.y $e |- Y = ( ( ( C - B ) F ( A - B ) ) / 3 ) $.
    morlemj.z $e |- Z = ( ( ( A - C ) F ( B - C ) ) / 3 ) $.
    morlemj.a $e |- ( ph -> A e. CC ) $.
    morlemj.b $e |- ( ph -> B e. CC ) $.
    morlemj.c $e |- ( ph -> C e. CC ) $.
    morlemj.ab $e |- ( ph -> A =/= B ) $.
    morlemj.bc $e |- ( ph -> B =/= C ) $.
    morlemj.ca $e |- ( ph -> C =/= A ) $.
    morlemj.o $e |- ( ph -> ( ( B - A ) F ( C - A ) ) e. ( 0 (,) _pi ) ) $.
    morlemj.j $e |- J
        = ( ( ( exp ` ( _i x. ( 2 x. X ) ) )
        x. ( exp ` ( _i x. ( 2 x. Y ) ) ) )
        x. ( exp ` ( _i x. ( 2 x. Z ) ) ) ) $.
    $( Let ` X ` , ` Y ` , ` Z ` be one third of the angles of a positively
       oriented triangle with vertices ` A ` , ` B ` , ` C ` .  The product
       ` J ` of the rotation coefficients for twice these angles is the
       rotation by ` ( 2 x. ( _pi / 3 ) ) ` , so it is a cube root of unity
       other than ` 1 ` .  (Contributed by JAG, 13-Oct-2026.) $)
    morlemj $p |- ( ph
        -> ( J = ( exp ` ( _i x. ( 2 x. ( _pi / 3 ) ) ) ) /\ ( J ^ 3 ) = 1 /\ J
        =/= 1 ) ) $=
      ( ci c2 cpi c3 cdiv co cmul ce cfv wceq cexp c1 wne a1i caddc oveq12d cc0
      cmin cioo wcel cr elioore syl recnd ang180pos simp1d addcld simp2d cc 3cn
      3ne0 divdird oveq1d eqtrd eqcomd addassd addcomd simp3d 3eqtrd oveq2d 2cn
      divcld eqeltrd adddid ax-icn mulcld fveq2d efadd syl2anc cz pire 3z efexp
      mul12d divcan2d ef2pi cre cneg ccos csin efival 2re 3re redivcld remulcld
      recoscld resincld crre cos2t csqrt sincos3rdpi simpri halfre mulassd 1cnd
      sqvald 2ne0 mullidd negsubdi2d 2halves pncan2d renegcld 0red 1red clt wbr
      negeqd halfgt0 lt0neg2d mpbid 0lt1 lttrd ltned eqnetrd re1 eqcomi neeqtrd
      neneqd wi fveq2 mtod neqned 3jca ) AHUDUEUFUGUHUIZUJUIZUJUIZUKULZUMHUGUNU
      IZUOUMHUOUPAHUDUEIUJUIZUJUIZUKULUDUEJUJUIZUJUIZUKULUJUIZUDUEKUJUIZUJUIZUK
      ULZUJUIZUUJHUUTUMAUCUQAUUJUUTAUUJUUMUUOURUIZUURURUIZUKULZUUTAUUIUVBUKAUUI
      UDUULUUNURUIZUUQURUIZUJUIZUVBAUUHUVEUDUJAUUHUEIJURUIZKURUIZUJUIZUVEAUVIUU
      HAUVHUUGUEUJAUVHEDVAUIFDVAUIGUIZUGUHUIZFEVAUIDEVAUIGUIZUGUHUIZURUIZDFVAUI
      EFVAUIGUIZUGUHUIZURUIZUVJUVLURUIZUVOURUIZUGUHUIZUUGAUVGUVNKUVPURAIUVKJUVM
      URIUVKUMAMUQZJUVMUMANUQZUSKUVPUMAOUQZUSAUVTUVQAUVTUVRUGUHUIZUVPURUIUVQAUV
      RUVOUGAUVJUVLAUVJAUVJUTUFVBUIZVCUVJVDVCUBUVJUTUFVEVFVGZAUVLAUVLUWEVCZUVLV
      DVCAUWGUVOUWEVCZUVLUVOURUIZUVJURUIZUFUMZABCDEFGLPQRSTUAUBVHZVIUVLUTUFVEVF
      VGZVJAUVOAUWHUVOVDVCAUWGUWHUWKUWLVKUVOUTUFVEVFVGZUGVLVCAVMUQZUGUTUPAVNUQZ
      VOAUWDUVNUVPURAUVJUVLUGUWFUWMUWOUWPVOVPVQVRAUVSUFUGUHAUVSUVJUWIURUIUWJUFA
      UVJUVLUVOUWFUWMUWNVSAUVJUWIUWFAUVLUVOUWMUWNVJVTAUWGUWHUWKUWLWAWBVPWBWCVRA
      UVIUEUVGUJUIZUUQURUIUVEAUEUVGKUEVLVCAWDUQZAIJAIUVKVLUWAAUVJUGUWFUWOUWPWEW
      FZAJUVMVLUWBAUVLUGUWMUWOUWPWEWFZVJAKUVPVLUWCAUVOUGUWNUWOUWPWEWFZWGAUWQUVD
      UUQURAUEIJUWRUWSUWTWGVPVQVQWCAUVFUDUVDUJUIZUURURUIUVBAUDUVDUUQUDVLVCAWHUQ
      ZAUULUUNAUEIUWRUWSWIZAUEJUWRUWTWIZVJAUEKUWRUXAWIZWGAUXBUVAUURURAUDUULUUNU
      XCUXDUXEWGVPVQVQWJAUVCUVAUKULZUUSUJUIZUUTAUVAVLVCUURVLVCUVCUXHUMAUUMUUOAU
      DUULUXCUXDWIZAUDUUNUXCUXEWIZVJAUDUUQUXCUXFWIUVAUURWKWLAUXGUUPUUSUJAUUMVLV
      CUUOVLVCUXGUUPUMUXIUXJUUMUUOWKWLVPVQVQVRVQZAUUKUUJUGUNUIZUOAHUUJUGUNUXKVP
      AUXLUGUUIUJUIZUKULZUDUEUFUJUIZUJUIZUKULZUOAUXNUXLAUUIVLVCUGWMVCZUXNUXLUMA
      UDUUHUXCAUEUUGUWRAUFUGAUFUFVDVCAWNUQZVGZUWOUWPWEZWIZWIUXRAWOUQUUIUGWPWLVR
      AUXMUXPUKAUXMUDUGUUHUJUIZUJUIUXPAUGUDUUHUWOUXCUYBWQAUYCUXOUDUJAUYCUEUGUUG
      UJUIZUJUIUXOAUGUEUUGUWOUWRUYAWQAUYDUFUEUJAUFUGUXTUWOUWPWRWCVQWCVQWJUXQUOU
      MAWSUQWBVQAHUOAHUOUMZHWTULZUOWTULZUMZAUYFUYGAUYFUOUYGAUYFUOUEUHUIZXAZUOAU
      YFUEUYIUEUNUIZUJUIZUOVAUIZUYJAUYFUUHXBULZUYMAUYFUYNUDUUHXCULZUJUIURUIZWTU
      LZUYNAHUYPWTAHUUJUYPUXKAUUHVLVCUUJUYPUMUYBUUHXDVFVQWJAUYNVDVCUYOVDVCUYQUY
      NUMAUUHAUEUUGUEVDVCAXEUQAUFUGUXSUGVDVCAXFUQUWPXGXHZXIAUUHUYRXJUYNUYOXKWLV
      QAUYNUEUUGXBULZUEUNUIZUJUIZUOVAUIZUYMAUUGVLVCUYNVUBUMUYAUUGXLVFAVUAUYLUOV
      AAUYTUYKUEUJAUYSUYIUEUNUYSUYIUMZAUUGXCULUGXMULUEUHUIUMVUCXNXOUQVPWCVPVQVQ
      AUYMUYIUOVAUIZUYJAUYLUYIUOVAAUYLUOUYIUJUIZUYIAUYLUEUYIUYIUJUIZUJUIZUEUYIU
      JUIZUYIUJUIZVUEAUYKVUFUEUJAUYIAUYIUYIVDVCAXPUQZVGZXSWCAVUIVUGAUEUYIUYIUWR
      VUKVUKXQVRAVUHUOUYIUJAUOUEAXRZUWRUEUTUPAXTUQWRVPWBAUYIVUKYAVQVPAVUDUOUYIV
      AUIZXAZUYJAVUNVUDAUOUYIVULVUKYBVRAVUMUYIAVUMUYIUYIURUIZUYIVAUIZUYIAVUPVUM
      AVUOUOUYIVAAUOVLVCVUOUOUMVULUOYCVFVPVRAUYIUYIVUKVUKYDVQYJVQVQVQAUYJUOAUYI
      VUJYEZAUYJUTUOVUQAYFAYGAUTUYIYHYIZUYJUTYHYIVURAYKUQAUYIVUJYLYMUTUOYHYIAYN
      UQYOYPYQUOUYGUMAUYGUOYRYSUQYTUUAUYEUYHUUBAHUOWTUUCUQUUDUUEUUF $.
  $}


  ${
    mul1subeqd.s $e |- ( ph -> S e. CC ) $.
    mul1subeqd.t $e |- ( ph -> T e. CC ) $.
    mul1subeqd.1 $e |- ( ph -> ( S x. T ) = U ) $.
    $( If ` ( S x. T ) = U ` , then ` ( S x. ( 1 - T ) ) = ( S - U ) ` .
       (Deduction form.)  (Contributed by JAG, 13-Oct-2026.) $)
    mul1subeqd $p |- ( ph -> ( S x. ( 1 - T ) ) = ( S - U ) ) $=
      ( c1 cmin co cmul 1cnd subdid mulridd oveq12d eqtrd ) ABHCIJKJBHKJZBCKJZI
      JBDIJABHCEALFMAQBRDIABENGOP $.
  $}


  ${
    cubm1d.s $e |- ( ph -> S e. CC ) $.
    $( The factorization of ` ( ( S ^ 3 ) - 1 ) ` over its root ` 1 ` .
       (Deduction form.)  (Contributed by JAG, 13-Oct-2026.) $)
    cubm1d $p |- ( ph -> ( ( S - 1 ) x. ( ( ( S ^ 2 ) + S ) + 1 ) )
        = ( ( S ^ 3 ) - 1 ) ) $=
      ( c1 cmin co c2 cexp caddc cmul c3 1cnd addcld subdird adddid a1i oveq12d
      sqcld eqtrd cc0 mulcomd wceq 2p1e3 oveq2i cn0 expp1d eqtr3d eqtr4d sqvald
      wcel 2nn0 eqcomd mulridd mullidd cc mulcld eqeltrd addassd addcomd subidd
      addsub4d oveq2d 3eqtrd subcld addridd ) ABDEFBGHFZBIFZDIFZJFZBKHFZVFIFZBI
      FZVHEFZVJDEFZAVIBVHJFZDVHJFZEFVMABDVHCALZAVGDAVFBABCRZCMZVQMZNAVOVLVPVHEA
      VOBVGJFZBDJFZIFVLABVGDCVSVQOAWAVKWBBIAWABVFJFZBBJFZIFVKABVFBCVRCOAWCVJWDV
      FIAWCVFBJFZVJABVFCVRUAABGDIFZHFZVJWEWGVJUBAWFKBHUCUDPABGCGUEUJAUKPUFUGZUH
      AVFWDABCUIULQSABCUMQSAVHVTUNQSAVMVNTIFZVNAVMVJVGIFZDVGIFZEFVNVGVGEFZIFWIA
      VLWJVHWKEAVJVFBAVJWEUOWHAVFBVRCUPUQZVRCURAVGDVSVQUSQAVJVGDVGWMVSVQVSVAAWL
      TVNIAVGVSUTVBVCAVNAVJDWMVQVDVESS $.
  $}


  ${
    morlemcyc.j $e |- ( ph -> J e. CC ) $.
    morlemcyc.c $e |- ( ph -> ( J ^ 3 ) = 1 ) $.
    morlemcyc.n $e |- ( ph -> J =/= 1 ) $.
    morlemcyc.s $e |- ( ph -> S e. CC ) $.
    $( For a cube root of unity ` J ` other than ` 1 ` , ` ( ( S ^ 3 ) - 1 ) `
       factors into the linear factors ` ( 1 - S ) ` , ` ( S - J ) ` and
       ` ( ( J ^ 2 ) - S ) ` , whose roots are the three cube roots of unity.
       (Contributed by JAG, 13-Oct-2026.) $)
    morlemcyc $p |- ( ph -> ( ( 1 - S ) x. ( ( S - J ) x. ( ( J ^ 2 ) - S ) ) )
        = ( ( S ^ 3 ) - 1 ) ) $=
      ( c1 cmin co c2 cexp cmul caddc cneg cc wcel wceq cc0 eqtrd mulsub adddid
      c3 sqcld syl22anc wn subne0d neneqd cubm1d oveq1d 1m1e0 a1i subcld addcld
      wo mul0ord mpbid ord mpd wb addeq0 syl2anc oveq2d mulneg2d mulridd negeqd
      1cnd eqtr3d sqvald eqcomd 2p1e3 oveq2i cn0 expp1d oveq12d addcomd addassd
      negdid negcld negsubd 3eqtrd eqtr4d negsubdi2d mulneg1d mulcld negnegd
      2nn0 ) AHBIJZBCIJCKLJZBIJMJZMJZBHIJZBKLJZBNJZHNJZMJZBUCLJHIJAWKWHWOOZMJWH
      WOMJZOZWPAWJWQWHMAWJBOZWMHNJZIJZWQAWJBWIMJBCMJNJZBBMJZWICMJZNJZIJZXBABPQZ
      CPQWIPQXHWJXGRGDACDUDZGBCWIBUAUEAXCWTXFXAIABWICNJZMJZXCWTABWICGXIDUBAXKBH
      OZMJZWTAXJXLBMAXJHNJZSRZXJXLRZACHIJZSRZUFXOAXQSACHDAVGZFUGUHAXRXOAXQXNMJZ
      SRXRXOUOAXTCUCLJZHIJZSACDUIAYBHHIJZSAYAHHIEUJYCSRAUKULTTAXQXNACHDXSUMAXJH
      AWICXIDUNZXSUNUPUQURUSAXJPQHPQXOXPUTYDXSXJHVAVBUQVCAXMBHMJZOWTABHGXSVDAYE
      BABGVEVFTTVHAXDWMXEHNAWMXDABGVIVJAXEYAHAYAXEACKHNJZLJZYAXEYGYARAYFUCCLVKV
      LULACKDKVMQAWGULVNVHVJETVOVOTAWQBXANJZOWTXAONJXBAWOYHABWMNJZHNJWOYHAYIWNH
      NABWMGABGUDZVPUJABWMHGYJXSVQVHVFABXAGAWMHYJXSUNZVRAWTXAABGVSYKVTWAWBVCAWH
      WOAHBXSGUMAWNHAWMBYJGUNXSUNZVDAWSWPOZOWPAWRYMAWLOZWOMJWRYMAYNWHWOMABHGXSW
      CUJAWLWOABHGXSUMZYLWDVHVFAWPAWLWOYOYLWEWFTWAABGUIT $.
  $}


  ${
    morlemne1.s $e |- ( ph -> S e. ( 0 (,) _pi ) ) $.
    $( A rotation by an angle ` S ` in the open interval ` ( 0 (,) _pi ) ` is
       not the identity: its coefficient ` ( exp `` ( _i x. S ) ) ` is not
       ` 1 ` .  (Contributed by JAG, 13-Oct-2026.) $)
    morlemne1 $p |- ( ph -> ( exp ` ( _i x. S ) ) =/= 1 ) $=
      ( ci cmul co ce cfv c1 wceq cim cc0 csin ccos caddc wcel cpi cr syl a1i
      cioo elioore recnd efival fveq2d recoscld resincld crim syl2anc eqtrd clt
      cc wbr sinq12gt0 gt0ne0d eqnetrd im1 eqcomi neeqtrd neneqd wi mtod neqned
      fveq2 ) ADBEFGHZIAVEIJZVEKHZIKHZJZAVGVHAVGLVHAVGBMHZLAVGBNHZDVJEFOFZKHZVJ
      AVEVLKABULPVEVLJABABLQUAFPZBRPCBLQUBSZUCBUDSUEAVKRPVJRPVMVJJABVOUFABVOUGV
      KVJUHUIUJAVJAVNLVJUKUMCBUNSUOUPLVHJAVHLUQURTUSUTVFVIVAAVEIKVDTVBVC $.
  $}


  ${
    morlemdne0.s $e |- ( ph -> S e. RR ) $.
    morlemdne0.t $e |- ( ph -> T e. RR ) $.
    morlemdne0.u $e |- ( ph -> U e. RR ) $.
    morlemdne0.ps $e |- ( ph -> 0 < S ) $.
    morlemdne0.pt $e |- ( ph -> 0 < T ) $.
    morlemdne0.pu $e |- ( ph -> 0 < U ) $.
    morlemdne0.1 $e |- ( ph -> ( ( S + T ) + U ) = ( _pi / 3 ) ) $.
    $( If ` S ` , ` T ` and ` U ` are positive reals summing to
       ` ( _pi / 3 ) ` , then
` ( 1 - ( ( exp `` ( _i x. ( 2 x. S ) ) ) x. ( exp `` ( _i x. ( 2 x. T ) ) ) )
) `
       is nonzero: the rotation by ` ( 2 x. ( S + T ) ) ` is not the identity.
       (Contributed by JAG, 13-Oct-2026.) $)
    morlemdne0 $p |- ( ph
        -> ( 1 - ( ( exp ` ( _i x. ( 2 x. S ) ) )
        x. ( exp ` ( _i x. ( 2 x. T ) ) ) ) ) =/= 0 ) $=
      ( c2 cmul co wcel a1i cpi clt wbr c3 c1 ci ce 1cnd cc ax-icn recnd mulcld
      cfv efcld caddc adddid oveq2d eqtrd fveq2d wceq efadd syl2anc eqcomd cioo
      2cn cc0 w3a 2re readdcld remulcld 2pos addgt0d mulgt0d cdiv pire 3re 3ne0
      cr wne redivcld wb ltaddpos mpbid breqtrd crp 2rp ltmul2d 2lt3 pipos 3pos
      divgt0d elrpd ltmul1d 3cn divcan2d lttrd 3jca cxr 0xr rexrd elioo2 mpbird
      morlemne1 eqnetrd necomd subne0d ) AUAUBLBMNZMNZUCUIZUBLCMNZMNZUCUIZMNZAU
      DAXEXHAXDAUBXCUBUEOAUFPZALBLUEOAVAPZABEUGZUHZUHZUJAXGAUBXFXJALCXKACFUGZUH
      ZUHZUJUHAXIUAAXIUBLBCUKNZMNZMNZUCUIZUAAYAXIAYAXDXGUKNZUCUIZXIAXTYBUCAXTUB
      XCXFUKNZMNYBAXSYDUBMALBCXKXLXOULUMAUBXCXFXJXMXPULUNUOAXDUEOXGUEOYCXIUPXNX
      QXDXGUQURUNUSAXSAXSVBQUTNOZXSVNOZVBXSRSZXSQRSZVCZAYFYGYHALXRLVNOAVDPZABCE
      FVEZVFZALXRYJYKVBLRSAVGPABCEFHIVHVIAXSLQTVJNZMNZQYLALYMYJAQTQVNOAVKPZTVNO
      AVLPZTVBVOAVMPZVPZVFYOAXRYMRSXSYNRSAXRXRDUKNZYMRAVBDRSZXRYSRSZJADVNOXRVNO
      YTUUAVQGYKDXRVRURVSKVTAXRYMLYKYRLWAOAWBPWCVSAYNTYMMNZQRALTRSZYNUUBRSUUCAW
      DPALTYMYJYPAYMYRAQTYOYPVBQRSAWEPVBTRSAWFPWGWHWIVSAQTAQYOUGTUEOAWJPYQWKVTW
      LWMAVBWNOZQWNOYEYIVQUUDAWOPAQYOWPVBQXSWQURWRWSWTXAXB $.
  $}


  ${
    morlemclr.a $e |- ( ph -> A e. CC ) $.
    morlemclr.b $e |- ( ph -> B e. CC ) $.
    morlemclr.r $e |- ( ph -> R e. CC ) $.
    morlemclr.e $e |- ( ph -> E e. CC ) $.
    morlemclr.d $e |- ( ph -> D e. CC ) $.
    morlemclr.1 $e |- ( ph
        -> ( A + ( E x. ( ( B + ( D x. ( R - B ) ) ) - A ) ) ) = R ) $.
    $( Clearing the denominator of a fixed-point equation.  If the similarity
       about ` B ` with factor ` D ` , followed by the similarity about ` A `
       with factor ` E ` , fixes ` R ` , then ` ( R x. ( 1 - ( E x. D ) ) ) `
       is a combination of ` A ` and ` B ` .  No division is needed.
       (Contributed by JAG, 13-Oct-2026.) $)
    morlemclr $p |- ( ph -> ( R x. ( 1 - ( E x. D ) ) )
        = ( ( ( 1 - E ) x. A ) + ( E x. ( ( 1 - D ) x. B ) ) ) ) $=
      ( c1 cmul co cmin caddc mulcld eqtrd wceq mulridd mulcomd oveq12d addcomd
      1cnd subdid subcld addcld affineequiv4 mpbird oveq1d oveq2d eqtr3d adddid
      mulassd eqcomd addassd eqtr4d subaddd ) AEMFDNOZPONOZEUTENOZPOZMFPOZBNOZF
      MDPOZCNOZNOZQOZAVAEMNOZEUTNOZPOVCAEMUTIAUEZAFDJKRZUFAVJEVKVBPAEIUAAEUTIVM
      UBUCSAVCVITVBVIQOZETAEVNAEVIVBQOZVNABFVGDENOZQOZBPOZNOZQOZEVOABFCDECPOZNO
      ZQOZBPOZNOZQOVTEAWEVSBQAWDVRFNAWCVQBPAWCVQTWCWBCQOTACWBHADWAKAECIHUGRZUDA
      WCCEDACWBHWFUHHIKUIUJUKULULLUMAVTVEFVQNOZQOZVOAVTWHTVTVSBQOTABVSGAFVRJAVQ
      BAVGVPAVFCAMDVLKUGHRZADEKIRZUHZGUGRZUDAVTBVQFABVSGWLUHGWKJUIUJAWHVEVHVBQO
      ZQOVOAWGWMVEQAWGVHFVPNOZQOWMAFVGVPJWIWJUNAWNVBVHQAVBWNAFDEJKIUOUPULSULAVE
      VHVBAVDBAMFVLJUGGRZAFVGJWIRZAUTEVMIRZUQURSUMAVIVBAVEVHWOWPUHZWQUDSUPAEVBV
      IIWQWRUSUJS $.
  $}


  ${
    morlemka.e $e |- ( ph -> E e. CC ) $.
    morlemka.d $e |- ( ph -> D e. CC ) $.
    morlemka.g $e |- ( ph -> G e. CC ) $.
    morlemka.j $e |- ( ph -> J = ( ( E x. D ) x. G ) ) $.
    morlemka.c $e |- ( ph -> ( J ^ 3 ) = 1 ) $.
    morlemka.n $e |- ( ph -> J =/= 1 ) $.
    $( An identity used by ~ morlemlinalg to collect the terms in ` A ` .  Let
       ` E ` , ` D ` , ` G ` be complex numbers whose product ` J ` is a cube
       root of unity other than ` 1 ` .  Then a polynomial in ` E ` , ` D ` ,
       ` G ` and ` J ` with the factor ` ( 1 - E ) ` equals
       ` ( ( E ^ 3 ) - 1 ) ` .  (Contributed by JAG, 13-Oct-2026.) $)
    morlemka $p |- ( ph
        -> ( ( ( ( ( E ^ 2 ) x. D ) x. ( 1 - ( D x. G ) ) )
        x. ( ( ( J x. G ) x. ( 1 - ( E x. D ) ) )
        + ( ( J ^ 2 ) x. ( 1 - ( G x. E ) ) ) ) ) x. ( 1 - E ) )
        = ( ( E ^ 3 ) - 1 ) ) $=
      ( cexp co cmul c1 cmin mulcld eqtrd oveq2d 3eqtrd eqeltrd mulassd mulcomd
      c2 caddc c3 cc eqcomd sqvald mul1subeqd sqcld eqidd oveq12d npncand mul4d
      oveq1d eqtr4d 1cnd subcld mul12d wceq 2p1e3 oveq2i a1i wcel expp1d eqtr3d
      cn0 2nn0 mulridd morlemcyc ) ACUDLMZBNMZOBDNMZPMZNMZEDNMZOCBNMZPMNMZEUDLM
      ZODCNMZPMNMZUEMZNMZOCPMZNMCEPMZVTCPMZNMZWENMWEWHNMCUFLMOPMAWDWHWENAWDCVTN
      MZVOOCENMZPMZNMZNMZCVONMZVTWKNMZNMWHAWDVPVQWKNMZNMVMVQNMZWLNMWMAWCWPVPNAW
      CVQVQWJNMZPMZWPAWCVQVTWANMZPMZWSAWCVQVTPMZVTWTPMZUEMXAAVSXBWBXCUEAVQVRVTA
      EDAEVRDNMZUGIAVRDACBFGQZHQUAZHQZXEAVQVRNMEDVRNMZNMEENMZVTAEDVRXFHXEUBAXHE
      ENAXHXDEADVRHXEUCAEXDIUHZRSAVTXIAEXFUIZUHZTUJAVTWAWTAEXFUKZADCHFQZAWTULUJ
      UMAVQVTWTXGXMAVTWAXMXNQUNRAWTWRVQPAWTXIWANMVQECNMZNMWRAVTXIWANXKUPAEEDCXF
      XFHFUOAXOWJVQNAECXFFUCSTSRAVQWJWRXGACEFXFQZAWRULUJUQSAVMVOVQWKAVLBACFUKGQ
      AOVNAURZABDGHQZUSZXGAOWJXQXPUSZUOAWQWIWLNAWQCVRNMZVQNMCVRVQNMZNMWIAVMYAVQ
      NAVMCCNMZBNMYAAVLYCBNACFUIUPACCBFFGUBRUPACVRVQFXEXGUBAYBVTCNAYBEXDNMXIVTA
      VREDXEXFHUTAXDEENXJSXLTSTUPTACVTVOWKFXMXSXTUOAWNWFWOWGNACVNEFXRACVNNMZXDE
      AXDYDACBDFGHUBUHXJRUJAVTWJCXMXPAVTWJNMCVTENMZNMCONMCAVTCEXMFXFUTAYEOCNAYE
      EUFLMZOAYFYEAEUDOUEMZLMZYFYEYHYFVAAYGUFELVBVCVDAEUDXFUDVHVEAVIVDVFVGUHJRS
      ACFVJTUJUMTUPAWHWEAWFWGACEFXFUSAVTCXMFUSQAOCXQFUSUCACEXFJKFVKT $.
  $}


  ${
    morlemkb.e $e |- ( ph -> E e. CC ) $.
    morlemkb.d $e |- ( ph -> D e. CC ) $.
    morlemkb.g $e |- ( ph -> G e. CC ) $.
    morlemkb.j $e |- ( ph -> J = ( ( E x. D ) x. G ) ) $.
    morlemkb.c $e |- ( ph -> ( J ^ 3 ) = 1 ) $.
    morlemkb.n $e |- ( ph -> J =/= 1 ) $.
    $( An identity used by ~ morlemlinalg to collect the terms in ` B ` .  Let
       ` E ` , ` D ` , ` G ` be complex numbers whose product ` J ` is a cube
       root of unity other than ` 1 ` .  Then a polynomial in ` E ` , ` D ` ,
       ` G ` and ` J ` with the factor ` ( 1 - D ) ` equals
       ` ( ( E ^ 3 ) x. ( ( D ^ 3 ) - 1 ) ) ` .  (Contributed by JAG,
       13-Oct-2026.) $)
    morlemkb $p |- ( ph
        -> ( ( ( ( ( E ^ 2 ) x. D ) x. ( 1 - ( G x. E ) ) )
        x. ( ( 1 - ( E x. D ) )
        + ( ( 1 - ( D x. G ) ) x. ( ( J ^ 2 ) x. E ) ) ) ) x. ( 1 - D ) )
        = ( ( E ^ 3 ) x. ( ( D ^ 3 ) - 1 ) ) ) $=
      ( cexp co cmul c1 cmin c3 mulcld subcld mulassd c2 caddc cc eqeltrd sqcld
      1cnd mulcomd eqcomd eqtrd oveq2d wceq 2p1e3 oveq2i a1i wcel expp1d eqtr3d
      cn0 3eqtrd mul1subeqd addcomd npncand oveq1d subdid eqtr4d mul32d oveq12d
      2nn0 3nn0 expcld morlemcyc ) ACUALMZBNMZODCNMZPMZNMZOCBNMZPMZOBDNMZPMZEUA
      LMZCNMZNMZUBMZNMZOBPMZNMCQLMZBEPMZWABPMZNMZNMZWFNMWGWJWFNMZNMWGBQLMOPMZNM
      AWEWKWFNAWEVPCWINMZNMZWGWHNMZWINMZWKAWDWNVPNAWDCWANMZVQPMZWNAWDWBVQPMZWSA
      WDVRWBOPMZUBMXAVRUBMWTAWCXAVRUBAWCWBVTNMXAAVTWBAOVSAUFZABDGHRZSAWACAEAEVQ
      DNMZUCIAVQDACBFGRZHRUDZUEZFRZUGAWBVSOXHXCAWBVSNMWACVSNMZNMWAENMZOAWACVSXG
      FXCTAXIEWANAXIXDEAXDXIACBDFGHTUHAEXDIUHUIZUJAXJEQLMZOAXLXJAEUAOUBMZLMZXLX
      JXNXLUKAXMQELULUMUNAEUAXFUAURUOAVHUNZUPUQUHJUIUSUTUIUJAVRXAAOVQXBXESAWBOX
      HXBSVAAWBOVQXHXBXEVBUSAWBWRVQPAWACXGFUGVCUIACWABFXGGVDVEUJAVPCNMZWINMWOWQ
      AVPCWIAVMVOAVLBACFUEZGRAOVNXBADCHFRZSZRFAWABXGGSZTAXPWPWINAXPVLBVONMZNMZC
      NMVLCNMZYANMWPAVPYBCNAVLBVOXQGXSTVCAVLYACXQABVOGXSRFVFAYCWGYAWHNAWGYCACXM
      LMZWGYCYDWGUKAXMQCLULUMUNACUAFXOUPUQUHABVNEGXRABVNNMZXIEAVSCNMYEXIABDCGHF
      TAVSCXCFUGUQXKUIUTVGUSVCUQAWGWHWIACQFQURUOAVIUNVJZABEGXFSZXTTUSVCAWGWJWFY
      FAWHWIYGXTRZAOBXBGSZTAWLWMWGNAWLWFWJNMWMAWJWFYHYIUGABEXFJKGVKUIUJUS $.
  $}


  ${
    morlemkc.e $e |- ( ph -> E e. CC ) $.
    morlemkc.d $e |- ( ph -> D e. CC ) $.
    morlemkc.g $e |- ( ph -> G e. CC ) $.
    morlemkc.gn $e |- ( ph -> G =/= 0 ) $.
    morlemkc.j $e |- ( ph -> J = ( ( E x. D ) x. G ) ) $.
    morlemkc.c $e |- ( ph -> ( J ^ 3 ) = 1 ) $.
    morlemkc.n $e |- ( ph -> J =/= 1 ) $.
    $( An identity used by ~ morlemlinalg to collect the terms in ` C ` .  Let
       ` E ` , ` D ` , ` G ` be complex numbers, ` G ` nonzero, whose product
       ` J ` is a cube root of unity other than ` 1 ` .  Then a polynomial in
       ` E ` , ` D ` , ` G ` and ` J ` with the factor ` ( 1 - G ) ` equals
       ` ( 1 - ( ( E ^ 3 ) x. ( D ^ 3 ) ) ) ` .  (Contributed by JAG,
       13-Oct-2026.) $)
    morlemkc $p |- ( ph
        -> ( ( ( ( ( E ^ 2 ) x. D ) x. ( 1 - ( E x. D ) ) )
        x. ( ( ( 1 - ( G x. E ) ) x. D ) + ( ( 1 - ( D x. G ) ) x. J ) ) )
        x. ( 1 - G ) ) = ( 1 - ( ( E ^ 3 ) x. ( D ^ 3 ) ) ) ) $=
      ( cexp co cmul c1 cmin c3 mulcld eqtrd c2 caddc sqcld 1cnd subcld eqeltrd
      cc addcld cn0 wcel a1i expcld cz 3z expne0d mulcomd mulassd eqtr3d eqcomd
      mul1subeqd eqidd oveq12d npncand mul12d oveq2d 3eqtrd eqtr4d mul4d oveq1d
      3nn0 sqvald sqmuld wceq 2p1e3 oveq2i 2nn0 expp1d mullidd morlemcyc subdid
      mulridd mulexpd mulcanad ) ACUAMNZBONZPCBONZQNZONZPDCONZQNZBONZPBDONZQNZE
      ONZUBNZONZPDQNZONZPCRMNZBRMNZONZQNZDRMNZAWPWQAWHWOAWEWGAWDBACFUCZGSZAPWFA
      UDZACBFGSZUEZSAWKWNAWJBAPWIXFADCHFSZUEZGSAWMEAPWLXFABDGHSZUEZAEWFDONZUGJA
      WFDXGHSUFZSUHSAPDXFHUEZSAPXAXFAWSWTACRFRUIUJAVJUKZULABRGXPULSZUEADRHXPULZ
      ADRHIRUMUJAUNUKUOAXCWRONZXCPQNZXCXBONZAXSXCWEBONZWGPEDONZQNZONZONZWQONZON
      ZXTAWRYGXCOAWPYFWQOAWPWHBYDONZONYFAWOYIWHOAWOBBYCONZQNZYIAWOBEQNZEEWLONZQ
      NZUBNBYMQNYKAWKYLWNYNUBAWKBWJONYLAWJBXJGUPABWIEGXIABWIONZCWLONZEAWLCONYOY
      PABDCGHFUQAWLCXKFUPURAYPXMEAXMYPACBDFGHUQUSAEXMJUSZTTUTTAWNEWMONYNAWMEXLX
      NUPAEWLYMXNXKAYMVAUTTVBABEYMGXNAEWLXNXKSVCAYMYJBQAEBDXNGHVDVEVFABYCYJGAED
      XNHSZAYJVAUTVGVEAWEWGBYDXEXHGAPYCXFYRUEZVHTVIVEAXCYFONZWQONZYHXTAXCYFWQXR
      AYBYEAWEBXEGSZAWGYDXHYSSZSXOUQAUUADEQNZEUAMNZDQNZONZWQONWQUUGONXTAYTUUGWQ
      OAXCYBONZYEONZYTUUGAXCYBYEXRUUBUUCUQAUUIDUUEONZYEONDWGONZUUEYDONZONUUGAUU
      HUUJYEOAUUHXCWDBUAMNZONZONZUUJAYBUUNXCOAYBWDBBONZONUUNAWDBBXDGGUQAUUMUUPW
      DOABGVKVEVGVEAUUJUUNXCONZUUOAUUJDUUNDUAMNZONZONUUNDUURONZONUUQAUUEUUSDOAU
      UEXMUAMNWFUAMNZUURONUUSAEXMUAMJVIAWFDXGHVLAUVAUUNUUROACBFGVLVIVFVEADUUNUU
      RHAWDUUMXDABGUCSZADHUCZVDAUUTXCUUNOAUUTUURDONZXCADUURHUVCUPADUAPUBNZMNZXC
      UVDUVFXCVMAUVERDMVNVOUKADUAHUAUIUJAVPUKZVQURVGVEVFAUUNXCUVBXRUPTVGVIADUUE
      WGYDHAEXNUCZXHYSVHAUUKUUDUULUUFOADWFEHXGADWFONXMEADWFHXGUPYQTUTAUUEYCDUVH
      YRAUUEEONZDONZUUEYCONDAUUEEDUVHXNHUQAUVJPDONDAUVIPDOAUVIERMNZPAUVKUVIAEUV
      EMNZUVKUVIUVLUVKVMAUVEREMVNVOUKAEUAXNUVGVQURUSKTVIADHVRTURUTVBVFURVIAUUGW
      QAUUDUUFADEHXNUEAUUEDUVHHUESXOUPADEXNKLHVSVFURTAYAXCPONZXCXAONZQNXTAXCPXA
      XRXFXQVTAUVMXCUVNPQAXCXRWAAUVNXAXCONZPAXCXAXRXQUPAUVKUVOPAUVKXMRMNWFRMNZX
      CONUVOAEXMRMJVIAWFDRXGHXPWBAUVPXAXCOACBRFGXPWBVIVFKURTVBTVGWC $.
  $}


  ${
    morlemlinalg.a $e |- ( ph -> A e. CC ) $.
    morlemlinalg.b $e |- ( ph -> B e. CC ) $.
    morlemlinalg.c $e |- ( ph -> C e. CC ) $.
    morlemlinalg.p $e |- ( ph -> P e. CC ) $.
    morlemlinalg.q $e |- ( ph -> Q e. CC ) $.
    morlemlinalg.r $e |- ( ph -> R e. CC ) $.
    morlemlinalg.e $e |- ( ph -> E e. CC ) $.
    morlemlinalg.d $e |- ( ph -> D e. CC ) $.
    morlemlinalg.g $e |- ( ph -> G e. CC ) $.
    morlemlinalg.en $e |- ( ph -> E =/= 0 ) $.
    morlemlinalg.dn $e |- ( ph -> D =/= 0 ) $.
    morlemlinalg.gn $e |- ( ph -> G =/= 0 ) $.
    morlemlinalg.j $e |- ( ph -> J = ( ( E x. D ) x. G ) ) $.
    morlemlinalg.cu $e |- ( ph -> ( J ^ 3 ) = 1 ) $.
    morlemlinalg.n $e |- ( ph -> J =/= 1 ) $.
    morlemlinalg.n1 $e |- ( ph -> ( 1 - ( D x. G ) ) =/= 0 ) $.
    morlemlinalg.n2 $e |- ( ph -> ( 1 - ( G x. E ) ) =/= 0 ) $.
    morlemlinalg.n3 $e |- ( ph -> ( 1 - ( E x. D ) ) =/= 0 ) $.
    morlemlinalg.1 $e |- ( ph
        -> ( A + ( E x. ( ( B + ( D x. ( R - B ) ) ) - A ) ) ) = R ) $.
    morlemlinalg.2 $e |- ( ph
        -> ( B + ( D x. ( ( C + ( G x. ( P - C ) ) ) - B ) ) ) = P ) $.
    morlemlinalg.3 $e |- ( ph
        -> ( C + ( G x. ( ( A + ( E x. ( Q - A ) ) ) - C ) ) ) = Q ) $.
    morlemlinalg.4 $e |- ( ph
        -> ( A
        + ( ( E ^ 3 )
        x. ( ( B
        + ( ( D ^ 3 ) x. ( ( C + ( ( G ^ 3 ) x. ( 0 - C ) ) ) - B ) ) )
        - A ) ) ) = 0 ) $.
    $( The algebraic step of the rotation proof of Morley's theorem, using
       field operations only.  Let ` E ` , ` D ` , ` G ` be nonzero complex
       numbers whose product ` J ` is a cube root of unity other than ` 1 ` ,
       and no product of two of them equal to ` 1 ` .  Let ` R ` , ` P ` ,
       ` Q ` be fixed by the composite similarities about ` A ` and ` B ` ,
       about ` B ` and ` C ` , and about ` C ` and ` A ` , with factors ` E ` ,
       ` D ` and ` G ` about ` A ` , ` B ` and ` C ` .  If the similarities
       about ` C ` , ` B ` and ` A ` with the cubes of these factors compose to
       a map fixing ` 0 ` , then
       ` ( ( P + ( J x. Q ) ) + ( ( J ^ 2 ) x. R ) ) = 0 ` .  (Contributed by
       JAG, 13-Oct-2026.) $)
    morlemlinalg $p |- ( ph -> ( ( P + ( J x. Q ) ) + ( ( J ^ 2 ) x. R ) )
        = 0 ) $=
      ( c2 cexp co cmul c1 cmin caddc cc0 wceq c3 cneg sqcld mulcld 1cnd subcld
      cc eqeltrd addcld adddid mulassd oveq2d mul4d eqtr3d eqtr4d 3eqtrd oveq1d
      mulcomd morlemclr eqcomd mul32d oveq12d addassd addcomd morlemkc morlemka
      eqtrd add4d adddird morlemkb cn0 wcel 3nn0 a1i expcld negsubdi2d mulneg1d
      mulneg2d negdid mulexpd mul1subeqd affineequiv4 mpbird 0cnd mul01d negeqd
      addridd neg0 cz 2z expne0d mulne0d mulcand mpbid ) AIUNUOUPZEUQUPZUREJUQU
      PZUSUPZURJIUQUPZUSUPZUQUPZURIEUQUPZUSUPZUQUPZUQUPZFKGUQUPZUTUPZKUNUOUPZHU
      QUPZUTUPZUQUPZYGVAUQUPZVBYLVAVBAYMVAYNAYMIVCUOUPZEVCUOUPZUQUPZURUSUPZDUQU
      PZVDZURYOUSUPZBUQUPZVDZUTUPZYOURYPUSUPZUQUPZCUQUPZVDZUTUPZVAAYMURYQUSUPZD
      UQUPZYOURUSUPZBUQUPZUTUPZYOYPURUSUPZUQUPZCUQUPZUTUPZUUIAYMXRYEUQUPZYBEUQU
      PZUQUPZURJUSUPZDUQUPZUQUPZUUSXTKUQUPZUQUPZUVCUQUPZUTUPZXRXTUQUPZKJUQUPZYE
      UQUPZUQUPZURIUSUPZBUQUPZUQUPZUVIYJYBUQUPZUQUPZUVNUQUPZUTUPZUTUPZXRYBUQUPZ
      YEUQUPZUREUSUPZCUQUPZUQUPZUWAXTYJIUQUPZUQUPZUQUPZUWDUQUPZUTUPZUTUPZUURAYM
      UWEUVDUTUPZUVGUVOUTUPZUTUPZUVRUWIUTUPZUTUPZUWKAYMYGYIUQUPZYGYKUQUPZUTUPUW
      PAYGYIYKAXRYFAXQEAIRVEZSVFZAYCYEAXTYBAURXSAVGZAEJSTVFVHZAURYAUXAAJITRVFVH
      ZVFZAURYDUXAAIERSVFZVHZVFZVFZAFYHOAKGAKYDJUQUPZVIUDAYDJUXETVFVJZPVFZVKZAY
      JHAKUXJVEZQVFZVLAUWQUWNUWRUWOUTAUWQYGFUQUPZYGYHUQUPZUTUPUWNAYGFYHUXHOUXKV
      LAUXOUWLUXPUWMUTAUXOUWBUWDEUVCUQUPZUTUPZUQUPZUWEUWBUXQUQUPZUTUPUWLAUXOUWB
      XTUQUPZFUQUPUWBXTFUQUPZUQUPUXSAYGUYAFUQAYGXRXTYBYEUQUPZUQUPZUQUPZUWAXTYEU
      QUPZUQUPZUYAAYFUYDXRUQAXTYBYEUXBUXCUXFVMVNAUVIUYCUQUPUYEUYGAXRXTUYCUWTUXB
      AYBYEUXCUXFVFVMAXRXTYBYEUWTUXBUXCUXFVOVPAUYGUWAYEXTUQUPZUQUPUYAAUYFUYHUWA
      UQAXTYEUXBUXFVTVNAUWAYEXTAXRYBUWTUXCVFZUXFUXBVMVQVRVSAUWBXTFAUWAYEUYIUXFV
      FZUXBOVMAUYBUXRUWBUQAUYBFXTUQUPUXRAXTFUXBOVTACDJFEMNOSTUKWAWIVNVRAUWBUWDU
      XQUYJAUWCCAUREUXASVHZMVFZAEUVCSAUVBDAURJUXATVHZNVFZVFVLAUXTUVDUWEUTAUWBEU
      QUPZUVCUQUPUXTUVDAUWBEUVCUYJSUYNVMAUYOUVAUVCUQAUYOUWAYEEUQUPUQUPUVAAUWAYE
      EUYIUXFSVMAXRYBYEEUWTUXCUXFSVOWIVSVPVNVRAUXPUVFUVCJUVNUQUPZUTUPZUQUPZUVGU
      VFUYPUQUPZUTUPUWMAUXPUVFYBGUQUPZUQUPZUYRAUXPYGKUQUPZGUQUPZUVFYBUQUPZGUQUP
      VUAAVUCUXPAYGKGUXHUXJPVMWBAVUBVUDGUQAVUBUUSXTUQUPZYBUQUPZKUQUPVUEKUQUPZYB
      UQUPVUDAYGVUFKUQAYGUUSYCUQUPZVUFAYGXRYEYCUQUPZUQUPVUHAYFVUIXRUQAYCYEUXDUX
      FVTVNAXRYEYCUWTUXFUXDVMVQAUUSXTYBAXRYEUWTUXFVFZUXBUXCVMVQVSAVUEYBKAUUSXTV
      UJUXBVFUXCUXJWCAVUGUVFYBUQAUUSXTKVUJUXBUXJVMVSVRVSAUVFYBGAUUSUVEVUJAXTKUX
      BUXJVFZVFZUXCPVMVRAUYTUYQUVFUQAUYTGYBUQUPUYQAYBGUXCPVTADBIGJNLPTRULWAWIVN
      WIAUVFUVCUYPVULUYNAJUVNTAUVMBAURIUXARVHZLVFZVFVLAUYSUVOUVGUTAUVFJUQUPZUVN
      UQUPUYSUVOAUVFJUVNVULTVUNVMAVUOUVLUVNUQAVUOUVIYEKUQUPZUQUPZJUQUPUVIVUPJUQ
      UPZUQUPUVLAUVFVUQJUQAXRYEXTKUWTUXFUXBUXJVOVSAUVIVUPJAXRXTUWTUXBVFZAYEKUXF
      UXJVFTVMAVURUVKUVIUQAVURYEUVJUQUPUVKAYEKJUXFUXJTVMAYEUVJUXFAKJUXJTVFZVTWI
      VNVRVSVPVNVRWDWIAUWRUVQUVNIUWDUQUPZUTUPZUQUPZUVRUVQVVAUQUPZUTUPUWOAUWRUVQ
      YEHUQUPZUQUPZVVCAUWRYGYJUQUPZHUQUPZUVQYEUQUPZHUQUPVVFAVVHUWRAYGYJHUXHUXMQ
      VMWBAVVGVVIHUQAVVGUVIYBUQUPZYEUQUPZYJUQUPVVJYJUQUPZYEUQUPVVIAYGVVKYJUQAYG
      XRYCUQUPZYEUQUPZVVKAVVNYGAXRYCYEUWTUXDUXFVMWBAVVJVVMYEUQAXRXTYBUWTUXBUXCV
      MVSVQVSAVVJYEYJAUVIYBVUSUXCVFUXFUXMWCAVVLUVQYEUQAVVLUVIYBYJUQUPZUQUPUVQAU
      VIYBYJVUSUXCUXMVMAVVOUVPUVIUQAYBYJUXCUXMVTVNWIVSVRVSAUVQYEHAUVIUVPVUSAYJY
      BUXMUXCVFZVFZUXFQVMVRAVVEVVBUVQUQAVVEHYEUQUPVVBAYEHUXFQVTABCEHILMQRSUJWAW
      IVNWIAUVQUVNVVAVVQVUNAIUWDRUYLVFVLAVVDUWIUVRUTAUVQIUQUPZUWDUQUPVVDUWIAUVQ
      IUWDVVQRUYLVMAVVRUWHUWDUQAVVRUVIUVPIUQUPZUQUPUVIYBUWFUQUPZUQUPUWHAUVIUVPI
      VUSVVPRVMAVVSVVTUVIUQAVVSUWFYBUQUPVVTAYJYBIUXMUXCRWCAUWFYBAYJIUXMRVFZUXCV
      TWIVNAXRXTYBUWFUWTUXBUXCVWAVOVRVSVPVNVRWDWIAUWPUVHUVOUTUPZUWEUTUPZUWOUTUP
      VWBUVRUTUPZUWJUTUPUWKAUWNVWCUWOUTAUWNUWEVWBUTUPZVWCAUWNUWEUVDUWMUTUPZUTUP
      VWEAUWEUVDUWMAUWBUWDUYJUYLVFZAUVAUVCAUUSUUTVUJAYBEUXCSVFZVFZUYNVFZAUVGUVO
      AUVFUVCVULUYNVFZAUVLUVNAUVIUVKVUSAUVJYEVUTUXFVFZVFZVUNVFZVKWEAVWFVWBUWEUT
      AVWBVWFAUVDUVGUVOVWJVWKVWNWEWBVNWIAUWEVWBVWGAUVHUVOAUVDUVGVWJVWKVKZVWNVKZ
      WFWIVSAVWBUWEUVRUWIVWPVWGAUVQUVNVVQVUNVFZAUWHUWDAUWAUWGUYIAXTUWFUXBVWAVFZ
      VFZUYLVFWJAVWDUVTUWJUTAUVHUVOUVRVWOVWNVWQWEVSVRWIAUVTUUNUWJUUQUTAUVHUUKUV
      SUUMUTAUUSUUTUVEUTUPZUQUPZUVCUQUPZUVHUUKAVXBUVAUVFUTUPZUVCUQUPUVHAVXAVXCU
      VCUQAUUSUUTUVEVUJVWHVUKVLVSAUVAUVFUVCVWIVULUYNWKWIAVXAUVBUQUPZDUQUPVXBUUK
      AVXAUVBDAUUSVWTVUJAUUTUVEVWHVUKVKVFUYMNVMAVXDUUJDUQAEIJKRSTUCUDUEUFWGVSVP
      VPAUVIUVKUVPUTUPZUQUPZUVNUQUPZUVSUUMAVXGUVLUVQUTUPZUVNUQUPUVSAVXFVXHUVNUQ
      AUVIUVKUVPVUSVWLVVPVLVSAUVLUVQUVNVWMVVQVUNWKWIAVXFUVMUQUPZBUQUPVXGUUMAVXF
      UVMBAUVIVXEVUSAUVKUVPVWLVVPVKVFVUMLVMAVXIUULBUQAEIJKRSTUDUEUFWHVSVPVPWDAU
      WAYEUWGUTUPZUQUPZUWDUQUPZUWJUUQAVXLUWBUWHUTUPZUWDUQUPUWJAVXKVXMUWDUQAUWAY
      EUWGUYIUXFVWRVLVSAUWBUWHUWDUYJVWSUYLWKWIAVXKUWCUQUPZCUQUPVXLUUQAVXKUWCCAU
      WAVXJUYIAYEUWGUXFVWRVKVFUYKMVMAVXNUUPCUQAEIJKRSTUDUEUFWLVSVPVPWDWIAUUNUUD
      UUQUUHUTAUUKYTUUMUUCUTAUUKYRVDZDUQUPYTAUUJVXODUQAVXOUUJAYQURAYOYPAIVCRVCW
      MWNAWOWPZWQZAEVCSVXPWQZVFZUXAWRWBVSAYRDAYQURVXSUXAVHZNWSWIAUUMUUAVDZBUQUP
      UUCAUULVYABUQAVYAUULAURYOUXAVXQWRWBVSAUUABAURYOUXAVXQVHZLWSWIWDAUUQUUFVDZ
      CUQUPUUHAUUPVYCCUQAUUPYOUUEVDZUQUPVYCAUUOVYDYOUQAVYDUUOAURYPUXAVXRWRWBVNA
      YOUUEVXQAURYPUXAVXRVHZWTWIVSAUUFCAYOUUEVXQVYEVFZMWSWIWDWIAUUIYSUUBUTUPZUU
      GUTUPZVDZVAAUUIVYGVDZUUHUTUPVYIAUUDVYJUUHUTAVYJUUDAYSUUBAYRDVXTNVFZAUUABV
      YBLVFZXAWBVSAVYGUUGAYSUUBVYKVYLVKAUUFCVYFMVFZXAVQAVYIVAVDZVAAVYHVAAVYHUUB
      UUGYSUTUPZUTUPZVAAVYHUUBYSUTUPZUUGUTUPUUBYSUUGUTUPZUTUPVYPAVYGVYQUUGUTAYS
      UUBVYKVYLWFVSAUUBYSUUGVYLVYKVYMWEAVYRVYOUUBUTAYSUUGVYKVYMWFVNVRAUUBYOUUEC
      UQUPZYPURJVCUOUPZUSUPZDUQUPZUQUPZUTUPZUQUPZUTUPZVYPVAAWUEVYOUUBUTAWUEUUGY
      QWUAUQUPZDUQUPZUTUPZVYOAWUEYOVYSUQUPZYOWUCUQUPZUTUPWUIAYOVYSWUCVXQAUUECVY
      EMVFZAYPWUBVXRAWUADAURVYTUXAAJVCTVXPWQZVHZNVFZVFZVLAWUJUUGWUKWUHUTAUUGWUJ
      AYOUUECVXQVYEMVMWBAWUHWUKAWUHYQWUBUQUPWUKAYQWUADVXSWUNNVMAYOYPWUBVXQVXRWU
      OVMWIWBWDWIAWUHYSUUGUTAWUGYRDUQAYQVYTURVXSWUMAYQVYTUQUPZKVCUOUPZURAWURWUQ
      AWURUXIVCUOUPZWUQAKUXIVCUOUDVSAWUSYDVCUOUPZVYTUQUPWUQAYDJVCUXETVXPXBAWUTY
      QVYTUQAIEVCRSVXPXBVSWIWIWBUEWIXCVSVNWIVNABYOWUDBUSUPZUQUPZUTUPZWUFVAAWVCW
      UFVBWVCWVBBUTUPVBABWVBLAYOWVAVXQAWUDBAVYSWUCWULWUPVKZLVHVFZWFAWVCBWUDYOAB
      WVBLWVEVKLWVDVXQXDXEABYOCYPDVYTVADUSUPZUQUPZUTUPZCUSUPZUQUPZUTUPZBUSUPZUQ
      UPZUTUPWVCVAAWVMWVBBUTAWVLWVAYOUQAWVKWUDBUSAWVKCYPWUBCUSUPZUQUPZUTUPZWUDA
      WVJWVOCUTAWVIWVNYPUQAWVHWUBCUSAWVHWUBVYTVAUQUPZUTUPZWUBVAUTUPWUBAWVHWVRVB
      WVHWVGDUTUPVBADWVGNAVYTWVFWUMAVADAXFZNVHVFZWFAWVHDVAVYTADWVGNWVTVKNWVSWUM
      XDXEAWVQVAWUBUTAVYTWUMXGVNAWUBWUOXIVRVSVNVNAWVPWUDVBWVPWVOCUTUPVBACWVOMAY
      PWVNVXRAWUBCWUOMVHVFZWFAWVPCWUBYPACWVOMWWAVKMWUOVXRXDXEWIVSVNVNUMVPVPVPWI
      XHVYNVAVBAXJWPWIWIWIAYNVAAYGUXHXGWBWIAYLVAYGAYIYKUXLUXNVKWVSUXHAXRYFUWTUX
      GAXQEUWSSAIUNRUAUNXKWNAXLWPXMUBXNAYCYEUXDUXFAXTYBUXBUXCUGUHXNUIXNXNXOXP
      $.
  $}


  ${
    $d A x y $.  $d B x y $.  $d C x y $.  $d P x y $.  $d Q x y $.
    $d R x y $.
    morlemlin.f $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    morlemlin.x $e |- X = ( ( ( B - A ) F ( C - A ) ) / 3 ) $.
    morlemlin.y $e |- Y = ( ( ( C - B ) F ( A - B ) ) / 3 ) $.
    morlemlin.z $e |- Z = ( ( ( A - C ) F ( B - C ) ) / 3 ) $.
    morlemlin.a $e |- ( ph -> A e. CC ) $.
    morlemlin.b $e |- ( ph -> B e. CC ) $.
    morlemlin.c $e |- ( ph -> C e. CC ) $.
    morlemlin.p $e |- ( ph -> P e. CC ) $.
    morlemlin.q $e |- ( ph -> Q e. CC ) $.
    morlemlin.r $e |- ( ph -> R e. CC ) $.
    morlemlin.ab $e |- ( ph -> A =/= B ) $.
    morlemlin.bc $e |- ( ph -> B =/= C ) $.
    morlemlin.ca $e |- ( ph -> C =/= A ) $.
    morlemlin.ra $e |- ( ph -> R =/= A ) $.
    morlemlin.rb $e |- ( ph -> R =/= B ) $.
    morlemlin.pb $e |- ( ph -> P =/= B ) $.
    morlemlin.pc $e |- ( ph -> P =/= C ) $.
    morlemlin.qc $e |- ( ph -> Q =/= C ) $.
    morlemlin.qa $e |- ( ph -> Q =/= A ) $.
    morlemlin.o $e |- ( ph -> ( ( B - A ) F ( C - A ) ) e. ( 0 (,) _pi ) ) $.
    morlemlin.1 $e |- ( ph -> ( ( B - A ) F ( R - A ) ) = X ) $.
    morlemlin.2 $e |- ( ph -> ( ( Q - A ) F ( C - A ) ) = X ) $.
    morlemlin.3 $e |- ( ph -> ( ( C - B ) F ( P - B ) ) = Y ) $.
    morlemlin.4 $e |- ( ph -> ( ( R - B ) F ( A - B ) ) = Y ) $.
    morlemlin.5 $e |- ( ph -> ( ( A - C ) F ( Q - C ) ) = Z ) $.
    morlemlin.6 $e |- ( ph -> ( ( P - C ) F ( B - C ) ) = Z ) $.
    morlemlin.j $e |- J
        = ( ( ( exp ` ( _i x. ( 2 x. X ) ) )
        x. ( exp ` ( _i x. ( 2 x. Y ) ) ) )
        x. ( exp ` ( _i x. ( 2 x. Z ) ) ) ) $.
    $( The vertices ` P ` , ` Q ` , ` R ` of the Morley triangle satisfy the
       linear relation ` ( ( P + ( J x. Q ) ) + ( ( J ^ 2 ) x. R ) ) = 0 ` ,
       where ` J ` is the product of the rotation coefficients for twice the
       trisected angles.  The hypotheses are those of ~ morleyR2 .  The
       relation follows from ~ morlemlinalg , applied to the rotations of
       ~ morlemfix3 and ~ morlemid , with ` J ` given by ~ morlemj .
       (Contributed by JAG, 13-Oct-2026.) $)
    morlemlin $p |- ( ph -> ( ( P + ( J x. Q ) ) + ( ( J ^ 2 ) x. R ) )
        = 0 ) $=
      ( ci c2 cmul co ce cfv cc wcel ax-icn a1i 2cn cmin cdiv wceq cc0 cpi cioo
      c3 cr elioore syl recnd 3cn wne 3ne0 divcld eqeltrd efcld caddc ang180pos
      mulcld simp1d simp2d efne0d cexp morlemj simp3d 3re redivcld clt eliooord
      c1 wbr simpld 3pos divgt0d breqtrrd addassd addcld addcomd eqcomd oveq12d
      wa divdird oveq1d 3eqtrd morlemdne0 morlemfix3 0cnd morlemid morlemlinalg
      eqtrd ) ADEFVBVCMVDVEZVDVEZVFVGZGHIVBVCLVDVEZVDVEZVFVGZVBVCNVDVEZVDVEZVFV
      GZKSTUAUBUCUDAYHAVBYGVBVHVIAVJVKZAVCLVCVHVIAVLVKZALEDVMVEFDVMVEJVEZVSVNVE
      ZVHLYPVOAPVKZAYOVSAYOAYOVPVQVRVEZVIZYOVTVIUNYOVPVQWAWBZWCZVSVHVIAWDVKZVSV
      PWEAWFVKZWGWHZWLWLZWIAYEAVBYDYMAVCMYNAMFEVMVEDEVMVEJVEZVSVNVEZVHMUUGVOAQV
      KZAUUFVSAUUFAUUFYRVIZUUFVTVIAUUIDFVMVEEFVMVEJVEZYRVIZUUFUUJWJVEZYOWJVEZVQ
      VOZABCDEFJOSTUAUEUFUGUNWKZWMZUUFVPVQWAWBZWCZUUBUUCWGWHZWLWLZWIAYKAVBYJYMA
      VCNYNANUUJVSVNVEZVHNUVAVOARVKZAUUJVSAUUJAUUKUUJVTVIAUUIUUKUUNUUOWNZUUJVPV
      QWAWBZWCZUUBUUCWGWHZWLWLZWIAYHUUEWOAYEUUTWOAYKUVGWOKYIYFVDVEYLVDVEVOAVAVK
      AKVBVCVQVSVNVEZVDVEVDVEVFVGVOZKVSWPVEXCVOZKXCWEZABCDEFJKLMNOPQRSTUAUEUFUG
      UNVAWQZWNAUVIUVJUVKUVLWRAMNLAMUUGVTUUHAUUFVSUUQVSVTVIAWSVKZUUCWTWHZANUVAV
      TUVBAUUJVSUVDUVMUUCWTWHZALYPVTYQAYOVSYTUVMUUCWTWHZAVPUUGMXAAUUFVSUUQUVMAV
      PUUFXAXDZUUFVQXAXDZAUUIUVQUVRXNUUPUUFVPVQXBWBXEVPVSXAXDAXFVKZXGUUHXHZAVPU
      VANXAAUUJVSUVDUVMAVPUUJXAXDZUUJVQXAXDZAUUKUWAUWBXNUVCUUJVPVQXBWBXEUVSXGUV
      BXHZAVPYPLXAAYOVSYTUVMAVPYOXAXDZYOVQXAXDZAYSUWDUWEXNUNYOVPVQXBWBXEUVSXGYQ
      XHZAMNWJVEZLWJVEZLMWJVEZNWJVEZUVHAUWJUWHAUWJLUWGWJVEUWHALMNUUDUUSUVFXIALU
      WGUUDAMNUUSUVFXJXKYCXLAUWJYPUUGWJVEZUVAWJVEZYOUUFWJVEZUUJWJVEZVSVNVEZUVHA
      UWIUWKNUVAWJALYPMUUGWJYQUUHXMUVBXMAUWOUWLAUWOUWMVSVNVEZUVAWJVEUWLAUWMUUJV
      SAYOUUFUUAUURXJUVEUUBUUCXOAUWPUWKUVAWJAYOUUFVSUUAUURUUBUUCXOXPYCXLAUWNVQV
      SVNAUWNYOUULWJVEUUMVQAYOUUFUUJUUAUURUVEXIAYOUULUUAAUUFUUJUURUVEXJXKAUUIUU
      KUUNUUOWRXQXPXQZYCXRANLMUVOUVPUVNUWCUWFUVTANLWJVEMWJVEZUWJUVHAUWRNUWIWJVE
      UWJANLMUVFUUDUUSXIANUWIUVFALMUUDUUSXJXKYCUWQYCXRALMNUVPUVNUVOUWFUVTUWCUWQ
      XRADYIEYFIEVMVEVDVEWJVEDVMVEVDVEWJVEIVOZEYFFYLGFVMVEVDVEWJVEEVMVEVDVEWJVE
      GVOZFYLDYIHDVMVEVDVEWJVEFVMVEVDVEWJVEHVOZABCDEFGHIJLMNOSTUAUBUCUDUEUFUGUH
      UIUJUKULUMUOUPUQURUSUTXSZWMAUWSUWTUXAUXBWNAUWSUWTUXAUXBWRABCDEFJVPLMNOPQR
      STUAAXTUEUFUGYAYB $.
  $}


  ${
    cubeq1facd.s $e |- ( ph -> S e. CC ) $.
    cubeq1facd.1 $e |- ( ph -> ( S ^ 3 ) = 1 ) $.
    $( If ` ( S ^ 3 ) = 1 ` , then ` ( S - 1 ) ` times
       ` ( ( ( S ^ 2 ) + S ) + 1 ) ` is zero.  (Deduction form.)  (Contributed
       by JAG, 13-Oct-2026.) $)
    cubeq1facd $p |- ( ph -> ( ( S - 1 ) x. ( ( ( S ^ 2 ) + S ) + 1 ) )
        = 0 ) $=
      ( c1 cmin co c2 cexp caddc cmul cc0 cubm1d oveq1d wceq 1m1e0 a1i 3eqtrd
      c3 ) ABEFGBHIGBJGEJGKGBSIGZEFGEEFGZLABCMATEEFDNUALOAPQR $.
  $}


  ${
    cubeq1absd.j $e |- ( ph -> J e. CC ) $.
    cubeq1absd.1 $e |- ( ph -> ( J ^ 3 ) = 1 ) $.
    $( A complex cube root of unity has absolute value ` 1 ` .  (Deduction
       form.)  (Contributed by JAG, 13-Oct-2026.) $)
    cubeq1absd $p |- ( ph -> ( abs ` J ) = 1 ) $=
      ( cabs cfv c1 cmin co cc0 wceq cexp caddc recnd readdcld a1i eqtrd eqtr3d
      cdiv c3 c2 cmul abscld 1cnd subcld resqcld sqge0d absge0d addge0d clt wbr
      1red 0lt1 addgegt0d gt0ne0d divcan4d cn0 wcel 3nn0 fveq2d abs1 cubeq1facd
      absexpd oveq1d div0d subeq0ad mpbid ) ABEFZGHIZJKVHGKAVIVHUALIZVHMIZGMIZU
      BIZVLSIZVIJAVIVLAVHGAVHABCUCZNZAUDZUEAVLAVKGAVJVHAVHVOUFZVOOZAULZONZAVLAV
      KGVSVTAVJVHVRVOAVHVOUGABCUHUIJGUJUKAUMPUNUOZUPAVNJVLSIJAVMJVLSAVHVPABTLIZ
      EFZVHTLIGABTCTUQURAUSPVCAWDGEFZGAWCGEDUTWEGKAVAPQRVBVDAVLWAWBVEQRAVHGVPVQ
      VFVG $.
  $}


  ${
    cubeq1sumd.j $e |- ( ph -> J e. CC ) $.
    cubeq1sumd.1 $e |- ( ph -> ( J ^ 3 ) = 1 ) $.
    cubeq1sumd.2 $e |- ( ph -> J =/= 1 ) $.
    $( A cube root of unity ` J ` other than ` 1 ` satisfies
       ` ( ( ( J ^ 2 ) + J ) + 1 ) = 0 ` .  (Deduction form.)  (Contributed by
       JAG, 13-Oct-2026.) $)
    cubeq1sumd $p |- ( ph -> ( ( ( J ^ 2 ) + J ) + 1 ) = 0 ) $=
      ( c1 cmin co c2 cexp caddc cmul cdiv cc0 sqcld addcld 1cnd subcld subne0d
      divcan3d cubeq1facd oveq1d div0d eqtrd eqtr3d ) ABFGHZBIJHZBKHZFKHZLHZUFM
      HZUINAUIUFAUHFAUGBABCOCPAQZPABFCULRZABFCULESZTAUKNUFMHNAUJNUFMABCDUAUBAUF
      UMUNUCUDUE $.
  $}


  ${
    morlemeqrot.u $e |- ( ph -> U e. CC ) $.
    morlemeqrot.v $e |- ( ph -> V e. CC ) $.
    morlemeqrot.w $e |- ( ph -> W e. CC ) $.
    morlemeqrot.j $e |- ( ph -> J e. CC ) $.
    morlemeqrot.1 $e |- ( ph -> ( J ^ 3 ) = 1 ) $.
    morlemeqrot.2 $e |- ( ph -> ( ( U + ( J x. V ) ) + ( ( J ^ 2 ) x. W ) )
        = 0 ) $.
    $( For a cube root of unity ` J ` , the relation
       ` ( ( U + ( J x. V ) ) + ( ( J ^ 2 ) x. W ) ) = 0 ` is preserved when
       ` U ` , ` V ` , ` W ` are replaced by ` W ` , ` U ` , ` V ` .
       (Contributed by JAG, 13-Oct-2026.) $)
    morlemeqrot $p |- ( ph -> ( ( W + ( J x. U ) ) + ( ( J ^ 2 ) x. V ) )
        = 0 ) $=
      ( cmul co c2 cexp caddc cc0 mulcld eqtrd c1 add32d addcomd oveq1d mulassd
      sqcld addcld adddid sqvald eqcomd oveq2d c3 mulcomd wceq 2p1e3 oveq2i a1i
      cn0 wcel 2nn0 expp1d eqtr3d eqtr4d mullidd oveq12d mul01d ) ACBLMZCNOMZDL
      MZPMZEPMZEVFPMZVHPMZQAVJVFEPMZVHPMVLAVFVHEACBIFRZAVGDACIUEZGRHUAAVMVKVHPA
      VFEVNHUBUCSACBCDLMZPMZVGELMZPMZLMZVJQAVTCVQLMZCVRLMZPMVJACVQVRIABVPFACDIG
      RZUFAVGEVOHRUGAWAVIWBEPAWAVFCVPLMZPMVIACBVPIFWCUGAWDVHVFPAVHWDAVHCCLMZDLM
      WDAVGWEDLACIUHUCACCDIIGUDSUIUJSACVGLMZELMZWBEACVGEIVOHUDAWGTELMEAWFTELAWF
      CUKOMZTAWFVGCLMZWHACVGIVOULACNTPMZOMZWHWIWKWHUMAWJUKCOUNUOUPACNINUQURAUSU
      PUTVAVBJSUCAEHVCSVAVDSAVTCQLMQAVSQCLKUJACIVESVAVA $.
  $}


  ${
    morlemeqd.u $e |- ( ph -> U e. CC ) $.
    morlemeqd.v $e |- ( ph -> V e. CC ) $.
    morlemeqd.w $e |- ( ph -> W e. CC ) $.
    morlemeqd.j $e |- ( ph -> J e. CC ) $.
    morlemeqd.1 $e |- ( ph -> ( J ^ 3 ) = 1 ) $.
    morlemeqd.2 $e |- ( ph -> ( ( ( J ^ 2 ) + J ) + 1 ) = 0 ) $.
    morlemeqd.3 $e |- ( ph -> ( ( U + ( J x. V ) ) + ( ( J ^ 2 ) x. W ) )
        = 0 ) $.
    $( If ` ( ( U + ( J x. V ) ) + ( ( J ^ 2 ) x. W ) ) = 0 ` , where ` J ` is
       a cube root of unity and a root of ` ( ( ( J ^ 2 ) + J ) + 1 ) ` , then
       the side ` ( V - W ) ` of the triangle with vertices ` U ` , ` V ` ,
       ` W ` is ` J ` times its side ` ( U - V ) ` .  (Contributed by JAG,
       13-Oct-2026.) $)
    morlemeqd $p |- ( ph -> ( V - W ) = ( J x. ( U - V ) ) ) $=
      ( cmin co cmul wceq caddc mulcld cc0 eqtrd subdid oveq2d addsubassd sqcld
      c2 cexp addcld addcomd morlemeqrot eqtr3d c1 1cnd adddird mullidd oveq12d
      addassd oveq1d mul02d eqtr4d addcand mpbid pncan2d subcld subaddd mpbird
      ) ADEMNCBDMNZONZPEVGQNZDPAVHECBONZCDONZMNZQNZDAVGVKEQACBDIFGUAUBAEVIQNZVJ
      MNZVLDAEVIVJHACBIFRZACDIGRZUCAVNVJDQNZVJMNDAVMVQVJMACUEUFNZDONZVMQNZVSVQQ
      NZPVMVQPAVTSWAAVMVSQNVTSAVMVSAEVIHVOUGZAVRDACIUDZGRZUHABCDEFGHIJLUIUJAVRC
      QNZUKQNZDONZWASAWGVSVJQNZDQNZWAAWGWEDONZUKDONZQNWIAWEUKDAVRCWCIUGAULGUMAW
      JWHWKDQAVRCDWCIGUMADGUNUOTAVSVJDWDVPGUPTAWGSDONSAWFSDOKUQADGURTUJUSAVSVMV
      QWDWBAVJDVPGUGUTVAUQAVJDVPGVBTUJTADEVGGHACVFIABDFGVCRVDVE $.
  $}


  ${
    morlemeqi.u $e |- ( ph -> U e. CC ) $.
    morlemeqi.v $e |- ( ph -> V e. CC ) $.
    morlemeqi.w $e |- ( ph -> W e. CC ) $.
    morlemeqi.j $e |- ( ph -> J e. CC ) $.
    morlemeqi.1 $e |- ( ph -> ( J ^ 3 ) = 1 ) $.
    morlemeqi.2 $e |- ( ph -> J =/= 1 ) $.
    morlemeqi.3 $e |- ( ph -> ( ( U + ( J x. V ) ) + ( ( J ^ 2 ) x. W ) )
        = 0 ) $.
    $( Three complex numbers ` U ` , ` V ` , ` W ` with
       ` ( ( U + ( J x. V ) ) + ( ( J ^ 2 ) x. W ) ) = 0 ` , for a cube root of
       unity ` J ` other than ` 1 ` , form an equilateral triangle: all three
       sides have the length of ` ( U - V ) ` .  (Contributed by JAG,
       13-Oct-2026.) $)
    morlemeqi $p |- ( ph
        -> ( ( abs ` ( W - U ) ) = ( abs ` ( U - V ) ) /\ ( abs ` ( V - W ) )
        = ( abs ` ( U - V ) ) ) ) $=
      ( cmin co cabs cfv wceq c1 cmul morlemeqd cubeq1sumd fveq2d subcld oveq1d
      morlemeqrot absmuld cubeq1absd 3eqtrd abscld recnd mullidd eqtrd eqcomd
      jca ) AEBMNZOPZBDMNZOPZQDEMNZOPZURQAURUPAURRUPSNZUPAURCUOSNZOPCOPZUPSNVAA
      UQVBOAECBDHFGIJACIJKUAZABCDEFGHIJLUETUBACUOIAEBHFUCZUFAVCRUPSACIJUGZUDUHA
      UPAUPAUOVEUIUJUKULUMAUTRURSNZURAUTCUQSNZOPVCURSNVGAUSVHOABCDEFGHIJVDLTUBA
      CUQIABDFGUCZUFAVCRURSVFUDUHAURAURAUQVIUIUJUKULUN $.
  $}


  ${
    $d A x y $.  $d B x y $.  $d C x y $.  $d P x y $.  $d Q x y $.
    $d R x y $.
    morleyR2.f $e |- F
        = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } )
        |-> ( Im ` ( log ` ( y / x ) ) ) ) $.
    morleyR2.x $e |- X = ( ( ( B - A ) F ( C - A ) ) / 3 ) $.
    morleyR2.y $e |- Y = ( ( ( C - B ) F ( A - B ) ) / 3 ) $.
    morleyR2.z $e |- Z = ( ( ( A - C ) F ( B - C ) ) / 3 ) $.
    morleyR2.a $e |- ( ph -> A e. CC ) $.
    morleyR2.b $e |- ( ph -> B e. CC ) $.
    morleyR2.c $e |- ( ph -> C e. CC ) $.
    morleyR2.p $e |- ( ph -> P e. CC ) $.
    morleyR2.q $e |- ( ph -> Q e. CC ) $.
    morleyR2.r $e |- ( ph -> R e. CC ) $.
    morleyR2.ab $e |- ( ph -> A =/= B ) $.
    morleyR2.bc $e |- ( ph -> B =/= C ) $.
    morleyR2.ca $e |- ( ph -> C =/= A ) $.
    morleyR2.ra $e |- ( ph -> R =/= A ) $.
    morleyR2.rb $e |- ( ph -> R =/= B ) $.
    morleyR2.pb $e |- ( ph -> P =/= B ) $.
    morleyR2.pc $e |- ( ph -> P =/= C ) $.
    morleyR2.qc $e |- ( ph -> Q =/= C ) $.
    morleyR2.qa $e |- ( ph -> Q =/= A ) $.
    morleyR2.o $e |- ( ph -> ( ( B - A ) F ( C - A ) ) e. ( 0 (,) _pi ) ) $.
    morleyR2.1 $e |- ( ph -> ( ( B - A ) F ( R - A ) ) = X ) $.
    morleyR2.2 $e |- ( ph -> ( ( Q - A ) F ( C - A ) ) = X ) $.
    morleyR2.3 $e |- ( ph -> ( ( C - B ) F ( P - B ) ) = Y ) $.
    morleyR2.4 $e |- ( ph -> ( ( R - B ) F ( A - B ) ) = Y ) $.
    morleyR2.5 $e |- ( ph -> ( ( A - C ) F ( Q - C ) ) = Z ) $.
    morleyR2.6 $e |- ( ph -> ( ( P - C ) F ( B - C ) ) = Z ) $.


    $( Morley's trisector theorem in the complex plane: the three points where
       adjacent angle trisectors of a triangle meet form an equilateral
       triangle.  The triangle has distinct vertices ` A ` , ` B ` , ` C ` and
       is positively oriented; ` F ` is the signed angle function, as in
       ~ ang2exp , and ` X ` , ` Y ` , ` Z ` are one third of the angles at
       ` A ` , ` B ` , ` C ` .  The point ` R ` is where the trisectors from
       ` A ` and ` B ` next to the side from ` A ` to ` B ` meet; likewise
       ` P ` for ` B ` and ` C ` , and ` Q ` for ` C ` and ` A ` .  The proof
       follows Connes: the composite rotations about consecutive vertices fix
       ` R ` , ` P ` and ` Q ` ( ~ morlemfix3 ), the rotations by twice the
       angles compose to the identity ( ~ morlemid ), which forces the linear
       relation of ~ morlemlin , and that relation says the triangle with
       vertices ` P ` , ` Q ` , ` R ` is equilateral ( ~ morlemeqi ).
       (Contributed by JAG, 13-Oct-2026.) $)
    morleyR2 $p |- ( ph
        -> ( ( abs ` ( R - P ) ) = ( abs ` ( P - Q ) ) /\ ( abs ` ( Q - R ) )
        = ( abs ` ( P - Q ) ) ) ) $=
      ( ci c2 cmul co ce cfv cc wcel ax-icn a1i 2cn cmin cdiv wceq cc0 cpi cioo
      c3 cr elioore syl recnd 3cn wne 3ne0 divcld eqeltrd efcld caddc ang180pos
      mulcld simp1d simp2d cexp c1 eqid morlemj simp3d morlemlin morlemeqi ) AG
      UTVAKVBVCZVBVCZVDVEZUTVALVBVCZVBVCZVDVEZVBVCZUTVAMVBVCZVBVCZVDVEZVBVCZHIU
      AUBUCAXFXIAXBXEAXAAUTWTUTVFVGAVHVIZAVAKVAVFVGAVJVIZAKEDVKVCFDVKVCJVCZVQVL
      VCZVFKXNVMAOVIAXMVQAXMAXMVNVOVPVCZVGXMVRVGUMXMVNVOVSVTWAVQVFVGAWBVIZVQVNW
      CAWDVIZWEWFWJWJWGAXDAUTXCXKAVALXLALFEVKVCDEVKVCJVCZVQVLVCZVFLXSVMAPVIAXRV
      QAXRAXRXOVGZXRVRVGAXTDFVKVCEFVKVCJVCZXOVGZXRYAWHVCXMWHVCVOVMZABCDEFJNRSTU
      DUEUFUMWIZWKXRVNVOVSVTWAXPXQWEWFWJWJWGWJAXHAUTXGXKAVAMXLAMYAVQVLVCZVFMYEV
      MAQVIAYAVQAYAAYBYAVRVGAXTYBYCYDWLYAVNVOVSVTWAXPXQWEWFWJWJWGWJAXJUTVAVOVQV
      LVCVBVCVBVCVDVEVMZXJVQWMVCWNVMZXJWNWCZABCDEFJXJKLMNOPQRSTUDUEUFUMXJWOZWPZ
      WLAYFYGYHYJWQABCDEFGHIJXJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPUQURUS
      YIWRWS $.
  $}
