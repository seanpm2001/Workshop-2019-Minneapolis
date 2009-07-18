	------------------------
----DOCUMENTATION-------
------------------------
export { "SCSCPConnection", "newConnection", "startServer", "remoteObject" }

beginDocumentation()
document { 
	Key => SCSCP,
	Headline => "SCSCP (Symbolic Computation Software Composability Protocol) support"
	}

document {
	Key => { newConnection, (newConnection, String), (newConnection, String, String), (newConnection, String, ZZ) },
	Headline => "Create a connection to an SCSCP server",
	Usage => "newConnection (host, port)",
	Inputs => { 
		"host" => String => { "The name or IP address of the host to connect to, with an optional colon followed by the number of the port" }, 
		"port" => {ofClass{String, ZZ}, ", providing the port number (this argument may be omitted)"}
	},
	Outputs => { SCSCPConnection => "The connection that was established" },
	"The port to connect to may be specified either by giving only one argument of the form host:port
	or by specifying the second argument. If neither of these is present, the port defaults to 26133.",
	SeeAlso => { (symbol SPACE, SCSCPConnection, Thing), (symbol SPACE, Manipulator, SCSCPConnection) }
	}

document {
	Key => { (symbol SPACE, Manipulator, SCSCPConnection) },
	Headline => "Close an SCSCP connection",
	Usage => "close s",
	Inputs => { 
		"close" => Manipulator => {"The manipulator called close"},
		"s" => SCSCPConnection => {"A connection, previously created with newConnection"}
	},
	SeeAlso => { (symbol SPACE, SCSCPConnection, Thing), newConnection }
 	}


document {
	Key => { SCSCPConnection, (symbol SPACE, SCSCPConnection, Thing), (symbol <==,SCSCPConnection,Thing), (symbol <===,SCSCPConnection,Thing) },
	Headline => "Execute computations using SCSCP",
	Usage => "s x",
	Inputs => { 
		"s" => SCSCPConnection => {"The server that should compute it"},
		"x" => Thing => {"The expression to be computed "}
	},
	Outputs => { Thing => "The result of the computation" },
	"As an example, we connect to a locally running SCSCP server: ",
	EXAMPLE { PRE ///
i1 : s = newConnection("127.0.0.1", 26135)

o1 = SCSCP Connection to GAP (4.dev) on 127.0.0.1:26135

o1 : SCSCPConnection

i2 : s(hold(2)+3)

o2 = 5

i3 : close s
/// },

	"We could also explicitly have a look at the openMath that's being passed around",
	EXAMPLE { PRE ///
i2 : o = openMath (hold(2)+3)

o2 = <OMA
       <OMS cd="arith1" name="plus"
       <OMI "2"
       <OMI "3"

o2 : XMLnode

i3 : s(o)

o3 = <OMOBJ
       <OMATTR
         <OMATP
           <OMS cd="scscp1" name="call_id"
           <OMSTR "1"
         <OMA
           <OMS cd="scscp1" name="procedure_completed"
           <OMI "5"

o3 : XMLnode

i4 : value oo

o4 = 5

	/// },

	"Another syntax offered is using the <== and <=== operators. The first of these denotes
	a computation that returns the computed object, whereas the second denotes a computation
	that returns a reference (i.e. a remote object)",
	EXAMPLE { PRE ///
i1 : s = newConnection("127.0.0.1", 26136)
 
o1 = SCSCP Connection to Magma (0.3.0) on 127.0.0.1:26136
 
o1 : SCSCPConnection
  
i2 : s <== hold(2)^32
 
o2 = 4294967296
 
i3 : s <=== hold(2)^333
 
o3 = << Remote Magma object >>
 
o3 : remoteObject
 
i4 : 2^301
 
o4 = 4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752
 
i5 : s <== oo44/oo45
 
o5 = 4294967296
 
o5 : QQ
	/// },
	SeeAlso => { newConnection, (symbol SPACE, Manipulator, SCSCPConnection), remoteObject }	
 	}


document {
	Key => { startServer, 1:startServer, (startServer, String), (startServer, ZZ) },
	Headline => "Start an SCSCP server",
	Usage => "startServer port",
	Inputs => { 
		"port" => {ofClass{String, ZZ}, ", providing the port number (defaults to 26133)"}
	},
	"The server will keep running indefinitely; it may be stoppend by sending a Ctrl-C. Furthermore,
	the server forks for every new incoming connection, so that it can serve many clients simultaneously.
	The amount of output printed to the screen is determined by the vaule of debugLevel.",
	EXAMPLE { PRE ///
i2 : debugLevel = 2;

i3 : startServer(26137)
[SCSCP][Server] Listening on :26137
[SCSCP][Server] Waiting for incoming connection 
[SCSCP][Server] Incoming connection. Forking. 
[SCSCP][handleIncoming 1] Handling new connection
[SCSCP][handleIncoming 1] Sending announcement
[SCSCP][handleIncoming 1] Waiting for version request...
[SCSCP][handleIncoming 1] Great! Compatible version: '1.3'
[SCSCP][Server] Waiting for incoming connection 
[SCSCP][handleIncoming 1] 'start' received
[SCSCP][handleProcedureCall 1] Evaluating procedure call...
[SCSCP][handleProcedureCall 1] Returning response...
[SCSCP][handleIncoming 1]  atEndOFFile
[SCSCP][Server] Child 1 terminated
 	///
	}
	}

document {
	Key => { remoteObject },
	Headline => "The class of all remote SCSCP objects",
	"As an example, we store three polynomials on a remote server, compute their product both locally and
	remotely, and then ask the remote server whether the results are equal. Note that <== and <=== may be
	used without their first argument if no confusion can arise about the SCSCP server where the 
	computation should take place.",
	EXAMPLE { PRE ///
i1 : loadPackage "SCSCP";

i2 : QQ[x];

i3 : p1 = x^2+1; p2 = x^3-1; p3 = x+17;

i4 : GAP = newConnection "127.0.0.1:26135";

i5 : gp1 = GAP <=== p1

o5 = << Remote GAP object >>

o5 : remoteObject

i6 : gp2 = GAP <=== p2; gp3 = GAP <=== p3;

i7 : gp = (gp1*gp2*gp3)

o7 = << Remote GAP object >>

o7 : remoteObject

i8 : p = p1*p2*p3;

i9 : <== (gp == p)

o9 = true
	///
	},
    "We create matrices in Macaulay2 and compute the order of the group they generate in GAP",
    EXAMPLE { PRE ///
i1 : loadPackage "SCSCP";

i2 : m1 = id_(QQ^10)^{1,6,2,7,3,8,4,9,5,0}

o2 = | 0 1 0 0 0 0 0 0 0 0 |
     | 0 0 0 0 0 0 1 0 0 0 |
     | 0 0 1 0 0 0 0 0 0 0 |
     | 0 0 0 0 0 0 0 1 0 0 |
     | 0 0 0 1 0 0 0 0 0 0 |
     | 0 0 0 0 0 0 0 0 1 0 |
     | 0 0 0 0 1 0 0 0 0 0 |
     | 0 0 0 0 0 0 0 0 0 1 |
     | 0 0 0 0 0 1 0 0 0 0 |
     | 1 0 0 0 0 0 0 0 0 0 |

              10        10
o2 : Matrix QQ   <--- QQ

i3 : m2 = id_(QQ^10)^{1,0,2,3,4,5,6,7,8,9}

o3 = | 0 1 0 0 0 0 0 0 0 0 |
     | 1 0 0 0 0 0 0 0 0 0 |
     | 0 0 1 0 0 0 0 0 0 0 |
     | 0 0 0 1 0 0 0 0 0 0 |
     | 0 0 0 0 1 0 0 0 0 0 |
     | 0 0 0 0 0 1 0 0 0 0 |
     | 0 0 0 0 0 0 1 0 0 0 |
     | 0 0 0 0 0 0 0 1 0 0 |
     | 0 0 0 0 0 0 0 0 1 0 |
     | 0 0 0 0 0 0 0 0 0 1 |

              10        10
o3 : Matrix QQ   <--- QQ

i4 : GAP = newConnection "127.0.0.1:26135"

o4 = SCSCP Connection to GAP (4.dev) on 127.0.0.1:26135

o4 : SCSCPConnection

i5 : G = GAP <=== matrixGroup({m1,m2})

o5 = << Remote GAP object >>

o5 : remoteObject

i6 : <== size G

o6 = 10080
    ///
    },
	SeeAlso => { newConnection, (symbol SPACE, Manipulator, SCSCPConnection), (symbol SPACE, SCSCPConnection, Thing) }	

}
 

undocumented { (identifyRemoteObjects, SCSCPConnection, XMLnode) }
undocumented{ (symbol *,remoteObject,remoteObject) }
undocumented{ (symbol *,remoteObject,Thing) }
undocumented{ (symbol +,remoteObject,remoteObject) }
undocumented{ (symbol +,remoteObject,Thing) }
undocumented{ (symbol -,remoteObject,remoteObject) }
undocumented{ (symbol -,remoteObject,Thing) }
undocumented{ (symbol /,remoteObject,remoteObject) }
undocumented{ (symbol /,remoteObject,Thing) }
undocumented{ (symbol ==,remoteObject,remoteObject) }
undocumented{ (symbol ==,remoteObject,Thing) }
undocumented{ (symbol and,remoteObject,remoteObject) }
undocumented{ (symbol and,remoteObject,Thing) }
undocumented{ (symbol or,remoteObject,remoteObject) }
undocumented{ (symbol or,remoteObject,Thing) }
undocumented{ (symbol *,Thing,remoteObject) }
undocumented{ (symbol +,Thing,remoteObject) }
undocumented{ (symbol -,Thing,remoteObject) }
undocumented{ (symbol /,Thing,remoteObject) }
undocumented{ (symbol ==,Thing,remoteObject) }
undocumented{ (symbol and,Thing,remoteObject) }
undocumented{ (symbol or,Thing,remoteObject) }
undocumented{ (openMath,remoteObject) }
undocumented{ (size,remoteObject) }

undocumented{ (net,SCSCPConnection) }
undocumented{ (symbol ===>,Thing,SCSCPConnection) } 
undocumented{ (symbol ==>,Thing,SCSCPConnection) } 
undocumented{ (symbol <==,remoteObject) } 
undocumented{ (symbol <===,remoteObject) } 
undocumented{ (net,remoteObject) }
