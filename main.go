package main

import (
	"bufio"
	"context"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"math"
	mrand "math/rand"
	"os"
	"strconv"
	"strings"
	"sync"
	"time"

	//good for debugging of data types and sizes
	//"unsafe"
	//"reflect" //TypeOf(var)

	libp2p "github.com/libp2p/go-libp2p"
	// Example how to use go-libp2p
	// https://github.com/libp2p/go-libp2p-examples/tree/master/echo

	/*
		// GX PACKAGE DEPENDENCIES: make, make deps
		golog "github.com/ipfs/go-log"
		crypto "github.com/libp2p/go-libp2p-crypto"
		host "github.com/libp2p/go-libp2p-host"
		net "github.com/libp2p/go-libp2p-net"
		peer "github.com/libp2p/go-libp2p-peer"
		pstore "github.com/libp2p/go-libp2p-peerstore"
		multiaddress "github.com/multiformats/go-multiaddr"
		gologging "github.com/whyrusleeping/go-logging"
		//pubsub "gx/ipfs/QmfB4oDUTiaGEqT13P1JqCEhqW7cB1wpKtq3PP4BN8PhQd/go-libp2p-pubsub"
	*/

	// TRY WITHOUT GX: GO MODULES DEPENDECIES
	// 1. go-gx uw: unwrite the dependecies from gx
	// 2. follow instruction for go mod

	golog "github.com/ipfs/go-log"
	crypto "github.com/libp2p/go-libp2p-crypto"
	host "github.com/libp2p/go-libp2p-host"
	net "github.com/libp2p/go-libp2p-net"
	peer "github.com/libp2p/go-libp2p-peer"
	pstore "github.com/libp2p/go-libp2p-peerstore"
	pubsub "github.com/libp2p/go-libp2p-pubsub"
	multiaddress "github.com/multiformats/go-multiaddr"
	gologging "github.com/whyrusleeping/go-logging"
)

// Define block structure for the blockchain
type Block struct {
	Index           int
	Timestamp       string
	File            string // must be a valid hash to a file stored in IPFS: Qm....
	Proposer        string // must be an IPFS peerID: Qm....; if joint: more than one, separated by ","
	AuthorMetrics   string
	ProposalMetrics string
	NetworkMetrics  string
	PrevHash        string
	Hash            string
}

// Streams: make global to enable closing it
var stream net.Stream

// The Blockchain is a series of validated Blocks
var Blockchain []Block

// This chain contains the new proposal (=unvalidated block)
var newBlockchainProposal []Block

// For voting: safe proposal in global variable to have it ready in terminal function:
var currentBCProposal []Block
var currentBlockProposal Block
var jointBCProposal []Block //for joint proposal: after pre-vote: send proposal to other peers
var currentPeerID2RemoveProposal string
var currentPeerID2RemoveProposer string
var currentPeerID2AddProposal string
var currentPeerID2AddProposer string

// for block verification: check if the final block is valid by comparing with proposal block
var verifySingleBlockProposals []Block
var verifyJointBlockProposals []Block

// Consensus
var openPreparedMsg []string
var openPreparedFailMsg []string
var singleProposalEnoughPrepared = bool(false)
var preparedHASH []string
var preparedPEERS []string
var preparedSent = bool(false)

var openPreparedJointMsg []string
var openPreparedFailJointMsg []string
var jointProposalEnoughPrepared = bool(false)
var preparedHASHjoint []string
var preparedPEERSjoint []string
var preparedSentjoint = bool(false)

var proposalTimeOut = float64(15) //time in seconds within consensus has to be reached
var votingTimeOut = float64(30) //time in seconds within vote has to be casted //TODO

// list of own block Proposals and correspondig votes: for main proposer to handle majorities
var myOpenBlockProposals []string
var posVotes []int
var negVotes []int

//list for add and remove peers proposals and votes
var myOpenPeerProposals []string
var posPeerVotes []int
var negPeerVotes []int

// for joint proposals: pre-votes
var myOpenJointBlockProposals []string
var myOpenJointBlockProposals_bytes []string
var posPreVotesJoint []int
var negPreVotesJoint []int

// for joint proposals: normal votes
var myOpenApprovedJointBlockProposals []string
var posVotesJoint []int
var negVotesJoint []int

// queue for received single block proposals
var openNewBlockProposals []string
var FinalBlockNewBlockProposals []string
var DeclinedNewBlockProposals []string

// queue for received peer proposals
var openRemoveOwnPeerAccountProposals []string
var openAddPeerAccountProposals []string
var openRemovePeerAccountProposals []string
var openDeclinedRemovePeerAccountProposals []string
var openFinalRemovePeerAccountProposals []string
var openFinalAddPeerAccountProposals []string
var openFinalAddPeerAccountProposalsDeclined []string

// queue for received joint block proposals
var openNewJointBlockProposals []string           //prevote
var openNewApprovedJointBlockProposals []string   //normal vote
var openNewJointBlockProposalsTokenFails []string //token fails of involved peer
var FinalBlockNewApprovedJointBlockProposals []string
var DeclinedBlockNewApprovedJointBlockProposals []string

// queue for received votes (blocks and peers)
var openVotesOnNewBlockProposals []string
var openPreVotesOnNewJointBlockProposals []string
var openVotesOnNewApprovedJointBlockProposals []string
var openVotesRemovePeerAccountProposals []string
var openVotesAddPeerAccountProposals []string

// Own Peerstore, add new peers with append(ConnectedPeers, newPeer)
// Implemented as "map" for better/faster retrieval
type ConnectedPeer map[string]interface{}

var ConnectedPeers []ConnectedPeer

// variable for author metrics
var ownPeerInfo map[string]interface{}

var GlobalPeerList []string
var myLocalPeers []string
var myLocalPeersbefore []string
var confirmedPeers2Add []string //majority for add
var removedPeers []string

// PubSub
var PubSubP2P *pubsub.PubSub
var pubsub_subsrc *pubsub.Subscription
var pubsub_topic = string("P2P-chain")

// Further global variables
var basicToken = int(4)             // token at beginning
var requStakeAddRemove = float64(1) // stake to propose add/remove new peer, corresponds validator reward

var requStake float64             // stake for single block proposal, corresponds validator reward
var myRequStakes []float64        // list of stakes for each own proposal; needed for reward later
var requStakeEachPeer float64     // stake for joint block proposal, corresponds validator reward
var myRequStakeEachPeer []float64 // list of stakes for each joint proposal; needed for reward later

var startingTimeProp []time.Time      //timestamp time.Time for measuring (single)
var startingTimeJointProp []time.Time //timestamp time.Time for measuring (joint)

//AuthorMetrics: all the information about the peer, as in ownPeerInfo
type AuthorMetrics struct {
	PeerID              string
	Port                int
	AuthorName          string //Username
	TokenBalance        int
	MemberSince         string
	TotalProposals      int
	ApprovedProposals   int
	DeclinedProposals   int
	ParticipationVoting float64
}

//ProposalMetrics
type ProposalMetrics struct {
	DepositedTokens   float64
	RequiredTime      string
	JointProposal     bool
	AcceptanceRate    float64
	ParticipationRate float64
}

// NetworkMetrics
type NetworkMetrics struct {
	ActiveNodes int
	//TotalNetworkProposals int
	//TotalNetworkTokens    int
}

// Mutex variable for mutual exclusion/race conditions
var mutex = &sync.Mutex{}

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// Definition of functions
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

// makeBasicHost creates a LibP2P host with a random peer ID listening on the
// given multiaddress. It uses secio for secure communication channels.
func makeBasicHost(listenPort int, secio bool, randseed int64) (host.Host, multiaddress.Multiaddr, []byte, error) {

	// If the seed is zero, use real cryptographic randomness. Otherwise, use a
	// deterministic randomness source to make generated keys stay the same  across multiple runs
	var r io.Reader
	if randseed == 0 {
		r = rand.Reader
	} else {
		r = mrand.New(mrand.NewSource(randseed))
	}

	// Generate a key pair for this host and use it to create a valid host ID.
	// RSA with 2048 bit and default exponent 65537
	priv, _, err := crypto.GenerateKeyPairWithReader(crypto.RSA, 2048, r) // _ is public key, not used here
	if err != nil {
		return nil, nil, nil, err
	}

	// constructs an address to which other peers can connect
	opts := []libp2p.Option{
		libp2p.ListenAddrStrings(fmt.Sprintf("/ip4/127.0.0.1/tcp/%d", listenPort)),
		libp2p.Identity(priv), //use the given private key to identify yourself
	}

	// create new basicHost with given address
	basicHost, err := libp2p.New(context.Background(), opts...)
	if err != nil {
		return nil, nil, nil, err
	}

	// Build host multiaddress
	hostAddr, _ := multiaddress.NewMultiaddr(fmt.Sprintf("/ipfs/%s", basicHost.ID().Pretty()))

	// Now build a full multiaddress to reach this host by encapsulating both addresses:
	addrs := basicHost.Addrs()
	var addr multiaddress.Multiaddr
	// select the address starting with "ip4"
	for _, i := range addrs {
		if strings.HasPrefix(i.String(), "/ip4") {
			addr = i
			break
		}
	}

	// show own address
	fullAddr := addr.Encapsulate(hostAddr)

	// Calculate your own peerID based on your fullAddress
	fullAddrString := fullAddr.String() // fullAddrString is a base58 string
	ipfsaddr_own, err := multiaddress.NewMultiaddr(fullAddrString)
	if err != nil {
		log.Fatalln(err)
	}

	pid_own, err := ipfsaddr_own.ValueForProtocol(multiaddress.P_IPFS)
	if err != nil {
		log.Fatalln(err)
	}

	// Create new Peer with metrics:
	t_p := time.Now()
	t_block := t_p.Format(time.RFC850) //string
	// read nickname
	stdReader0 := bufio.NewReader(os.Stdin)
	fmt.Println("Please enter your username:")
	nickname, err := stdReader0.ReadString('\n')
	if err != nil {
		log.Fatal(err)
	}
	nickname = strings.Replace(nickname, "\n", "", -1)

	// create new peer
	newPeer := &AuthorMetrics{pid_own, listenPort, string(nickname), int(basicToken), t_block, 0, 0, 0, 0.0}
	newPeer_parsed, err := json.Marshal(newPeer)
	if err != nil {
		panic(err)
	}
	log.Println("New peer successfully created!")

	// Tell new nodes how to connect with the host
	if secio {
		fmt.Printf("To connect, run \"go run main.go -l %d -d %s -secio\" on a different terminal\n", listenPort+1, fullAddr)
	} else {
		fmt.Printf("To connect, run \"go run main.go -l %d -d %s\" on a different terminal\n", listenPort+1, fullAddr)
	}

	return basicHost, fullAddr, newPeer_parsed, nil

} // end makeBasicHost

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

// handleStream is executed for each new incoming stream to the local peer.
// stream is used to exchange data between the local and remote peers
// using non blocking functions for reading and writing from this stream.
func handleStream(s net.Stream) {

	// This is executed by the first node/terminal firstly and later by every
	// other node/terminal that receives a new stream!
	// Create a buffer stream for non blocking read and write.
	// stream 's' will stay open until you close it (or the other side closes it)
	//rw := bufio.NewReadWriter(bufio.NewReader(s), bufio.NewWriter(s))
	log.Println("Got a new stream!")

	ownPeerInfo_handle := ConnectedPeers[0]

	// Start goroutines
	go handleTerminalInput(pubsub_subsrc, ownPeerInfo_handle)
	go readWriteProcessData(pubsub_subsrc, ownPeerInfo_handle)

} //end handleStream

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

//generate a new block with metrics
func generateBlock(oldBlock Block, link string, peerID_proposer string, AuthorMetrics string, ProposalMetrics string, NetworkMetrics string) (Block, error) {

	var newBlock Block
	t := time.Now()
	t_block := t.Format(time.RFC850) //string

	newBlock.Index = oldBlock.Index + 1
	newBlock.Timestamp = t_block
	newBlock.File = link
	newBlock.Proposer = peerID_proposer //if joint: IDs separated by "," in one string
	newBlock.AuthorMetrics = AuthorMetrics
	newBlock.ProposalMetrics = ProposalMetrics
	newBlock.NetworkMetrics = NetworkMetrics
	newBlock.PrevHash = oldBlock.Hash
	newBlock.Hash = calculateHash(newBlock)

	return newBlock, nil
} // end generateBlock

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

// SHA256 hashing
func calculateHash(block Block) string {
	// Hash all the data in the block, also the metrics
	record := string(block.Index) + block.Timestamp + block.File + block.Proposer + block.AuthorMetrics + block.ProposalMetrics + block.NetworkMetrics + block.PrevHash
	h := sha256.New()
	h.Write([]byte(record))
	hashed := h.Sum(nil)
	return hex.EncodeToString(hashed)
} //end calculatehash

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

// make sure block is valid by checking index, and comparing the hashes of the previous block
func isBlockValid(newBlock, oldBlock Block) bool {

	if oldBlock.Index+1 != newBlock.Index {
		return false
	}

	if oldBlock.Hash != newBlock.PrevHash {
		return false
	}

	if calculateHash(newBlock) != newBlock.Hash {
		return false
	}
	return true
} // end isBlockValid

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

//func unique returns a single slice of string where double elements are deleted
func unique(stringSlice []string) []string {
	keys := make(map[string]bool)
	list := []string{}
	for _, entry := range stringSlice {
		if _, value := keys[entry]; !value {
			keys[entry] = true
			list = append(list, entry)
		}
	}
	return list
}

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

//func difference returns the different entry/entries between two slices of strings: s1 = {A,B}, s2 = {A,B,C}: diff = {C}
func difference(a, b []string) []string {
	mb := map[string]bool{}
	for _, x := range b {
		mb[x] = true
	}
	var ab []string
	for _, x := range a {
		if _, ok := mb[x]; !ok {
			ab = append(ab, x)
		}
	}
	return ab
}

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

//handle terminal input/proposals + regular broadcasts of global chain and peer infos
func handleTerminalInput(pubsub_subsrc *pubsub.Subscription, ownPeerInfo map[string]interface{}) {

	//parse incoming sender peer data
	pid_own := ownPeerInfo["PeerID"].(string)


	//Broadcast latest valid/global chain every x seconds with other peers: "regularBroadcast"; they update if they do not have the latest version.
	go func() {
		for {
			time.Sleep(120 * time.Second) //TODO: ADJUST
			mutex.Lock()
			Blockchain_bytes, err := json.Marshal(Blockchain)
			if err != nil {
				log.Println(err)
			}
			mutex.Unlock()

			var msg_1 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "regularBroadcast;"
			msg_1.WriteString(senderID)
			msg_1.WriteString(switchcase)
			msg_1.WriteString(string(Blockchain_bytes))
			msg_1_send := msg_1.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_1_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

		}
	}()



	//PeersInNetwork
	go func() {
		for {

			time.Sleep(15 * time.Second) //every X seconds
			mutex.Lock()
			//Add own ID
			myLocalPeers := append(myLocalPeers, pid_own)

			//Add direct connected peers
			others := PubSubP2P.ListPeers(pubsub_topic)
			// convert []peer.ID to []string slice
			var others_string []string
			for j := 0; j < len(others); j++ {
				others_string = append(others_string, peer.IDB58Encode(others[j]))
				myLocalPeers = append(myLocalPeers, others_string[j])
			}
			mutex.Unlock()

			//If something has changed: send update; if not, send nothing!
			if len(myLocalPeersbefore) == 0 || len(myLocalPeersbefore) != len(myLocalPeers) {
				//fmt.Println("Number of local peers has changed!")

			/*				// ++++ COMMENT FROM HERE TO ENABLE ADDING OF PEERS WITH RAMDOM IDs++++++

							//Check if new peer was added
							if len(myLocalPeersbefore) < len(myLocalPeers) && len(GlobalPeerList) > 2 {
								// Check if new peer is on list of accepted new peers

								//get new stream ID
								peerIDnewStreams := difference(myLocalPeers, myLocalPeersbefore)

								if len(peerIDnewStreams) == 0 { //not empty
									continue
								} else {

									peerIDnewStream := string(peerIDnewStreams[0]) //only one inside
									newStreamInList := false
									//compare with list: confirmedPeers2Add
									for l := 0; l < len(confirmedPeers2Add); l++ {
										if confirmedPeers2Add[l] == peerIDnewStream {
											newStreamInList = true
										}
									}

									if newStreamInList == false {
										//fmt.Println("Got a stream that is not confirmed....remove it!")

										//send msg to new stream to close it!
										var msg_2 strings.Builder
										senderID := ownPeerInfo["PeerID"].(string)
										senderID = senderID + string(";")
										switchcase := "invalidPeerAdd;"
										msg_2.WriteString(senderID)
										msg_2.WriteString(switchcase)
										msg_2.WriteString(peerIDnewStream) //invalid peer
										msg_2_send := msg_2.String()

										// broadcast with PubSub
										pubsub_msg := []byte(msg_2_send)
										go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

										//remove from GlobalPeerList and network metrics!
										for k := 0; k < len(GlobalPeerList); k++ {
											if peerIDnewStream == GlobalPeerList[k] {
												copy(GlobalPeerList[k:], GlobalPeerList[k+1:])
												GlobalPeerList[len(GlobalPeerList)-1] = ""
												GlobalPeerList = GlobalPeerList[:len(GlobalPeerList)-1]
											}
										}

										//remove from local PeerList
										for k := 0; k < len(myLocalPeers); k++ {
											if peerIDnewStream == myLocalPeers[k] {
												copy(myLocalPeers[k:], myLocalPeers[k+1:])
												myLocalPeers[len(myLocalPeers)-1] = ""
												myLocalPeers = myLocalPeers[:len(myLocalPeers)-1]
											}
										}

									}
								}
							}

							// ++++ COMMENT UNTIL HERE TO ENABLE ADDING OF PEERS WITH RAMDOM IDs++++++

							*/


				//Update local
				myLocalPeersbefore = myLocalPeers

				//update global
				GlobalPeerList := append(GlobalPeerList, myLocalPeers...)
				GlobalPeerList = unique(GlobalPeerList)

				//For message transfer make Single string instead of []string slice
				mutex.Lock()
				var myLocalPeers_strg strings.Builder
				for k := 0; k < len(myLocalPeers); k++ {
					if k == len(myLocalPeers)-1 {
						myLocalPeers_strg.WriteString(myLocalPeers[k])
					} else {
						myLocalPeers_strg.WriteString(myLocalPeers[k] + string(","))
					}
				}
				myLocalPeers2 := myLocalPeers_strg.String()

				//For message transfer make Single string instead of []string slice
				var GlobalPeers_strg strings.Builder
				for k := 0; k < len(GlobalPeerList); k++ {
					if k == len(GlobalPeerList)-1 {
						GlobalPeers_strg.WriteString(GlobalPeerList[k])
					} else {
						GlobalPeers_strg.WriteString(GlobalPeerList[k] + string(","))
					}
				}
				GlobalPeerList2 := GlobalPeers_strg.String()
				mutex.Unlock()

				var msg_2 strings.Builder
				senderID := ownPeerInfo["PeerID"].(string)
				senderID = senderID + string(";")
				switchcase := "regularPeerUpdate;"
				msg_2.WriteString(senderID)
				msg_2.WriteString(switchcase)
				msg_2.WriteString(myLocalPeers2 + string(";"))
				msg_2.WriteString(GlobalPeerList2)
				msg_2_send := msg_2.String()

				// broadcast with PubSub
				pubsub_msg := []byte(msg_2_send)
				go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			} //end if changed

		}
	}()

	// Start a new reader to read in data from Terminal
	stdReader := bufio.NewReader(os.Stdin)

	for {

		time.Sleep(10 * time.Second) // delay a bit
		fmt.Println("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")
		fmt.Println("Welcome! Your peer account information/metrics are:")
		fmt.Println(ownPeerInfo)
		fmt.Println("To propose content changes done by only yourself press <S>")
		fmt.Println("To propose content changes done by you and others jointly press <J>")
		fmt.Println("To propose to add a new peer press <A>")
		fmt.Println("To propose to remove an existing peer press <R>")
		fmt.Println("To delete and remove your own account press <D>")
		fmt.Printf("Other directly connected PubSub peers in topic %s: %v\n", pubsub_topic, PubSubP2P.ListPeers(pubsub_topic))
		//fmt.Printf("All network-wide connected PubSub peers in topic %s: %v\n", pubsub_topic, len(GlobalPeerList))
		fmt.Println("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++")

		// Code for different actions; use later to distinguish
		inputType, err := stdReader.ReadString('\n')
		if err != nil {
			log.Fatal(err)
		}
		// parse incoming string response
		inputType = strings.Replace(inputType, "\n", "", -1)

		// Switch case: depending on terminal input start different actions
		switch inputType {

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		//remove own account
		case "D":
			fmt.Println("Are you sure you want to remove your own account from the network? This will reset your token account and requires an invitation plus majority vote of the network to come back!")
			fmt.Println("To confirm enter <yes>, otherwise enter anything else:")
			confirm_remove, err := stdReader.ReadString('\n')
			if err != nil {
				log.Fatal(err)
			}
			confirm_remove = strings.Replace(confirm_remove, "\n", "", -1)

			if strings.HasPrefix(confirm_remove, "yes") == true {

				fmt.Println("Checking requirements...")
				if len(myOpenBlockProposals) > 0 || len(myOpenPeerProposals) > 0 || len(myOpenJointBlockProposals) > 0 || len(myOpenApprovedJointBlockProposals) > 0 {
					fmt.Println("ERROR: you have open proposals. Wait until they are finished and try again!")
					continue
				}

				fmt.Printf("\x1b[33m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n") //31 red, 32 grren, 33 orange, 34 blue
				fmt.Printf("You confirmed to leave. The other peers will be informed, your account will be deleted and your connection disconnected...Goodbye!\n")
				fmt.Printf("\x1b[33m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n") //31 rot, 34 blue

				// inform other peers
				var msg_3 strings.Builder
				senderID := ownPeerInfo["PeerID"].(string)
				senderID = senderID + string(";")
				switchcase := "removeOwnPeerAccount"
				msg_3.WriteString(senderID)
				msg_3.WriteString(switchcase)
				msg_3_send := msg_3.String()

				// broadcast with PubSub
				pubsub_msg := []byte(msg_3_send)
				go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

				//Delay to give other peers time to remove from lists etc.
				time.Sleep(5 * time.Second)

				// Unsubscribe from PubSub topic, closes stream
				pubsub_subsrc.Cancel()

			} else {
				fmt.Println("You will stay in the network!")
				continue
			}

			// add peer
		case "A":
			fmt.Println("Enter the peerID of the peer you want to add: ")
			peerID_add, err := stdReader.ReadString('\n')
			if err != nil {
				log.Fatal(err)
			}
			peerID_add = strings.Replace(peerID_add, "\n", "", -1)

			if strings.HasPrefix(peerID_add, "Qm") == false {
				fmt.Println("ERROR: Invalid PeerID")
				continue

			} else {
				fmt.Printf("You propose to add PeerID %s.\nProcessing...\n", peerID_add)

				// Check if proposer has enough stake to make proposal
				TokenBalance := float64(ownPeerInfo["TokenBalance"].(float64))

				if TokenBalance < requStakeAddRemove {
					fmt.Println("Error! You do not have enough stake/deposit to make a proposal!")
					fmt.Printf("Your Token Balance is: %v\n", TokenBalance)
					continue

				} else {
					fmt.Println("Everything fine! You have enough tokens to make a proposal!")
					fmt.Println("Please provide some background information about the peer you want to add and justify your reason:")

					reason, err := stdReader.ReadString('\n')
					if err != nil {
						log.Fatal(err)
					}
					reason = strings.Replace(reason, "\n", "", -1)

					// update AuthorMETRICS: stake deposit and # proposals
					NewTokenBalance := TokenBalance - requStakeAddRemove
					ownPeerInfo["TokenBalance"] = interface{}(NewTokenBalance)

					numberOfProposals := float64(ownPeerInfo["TotalProposals"].(float64))
					NewNumberOfProposals := numberOfProposals + float64(1)
					ownPeerInfo["TotalProposals"] = interface{}(NewNumberOfProposals)

					// write new peerID into msg and send.
					var msg_4 strings.Builder
					senderID := ownPeerInfo["PeerID"].(string)
					senderID = senderID + string(";")
					proposerID := senderID
					switchcase := "addNewPeerProposal;"
					msg_4.WriteString(senderID)
					msg_4.WriteString(switchcase)
					msg_4.WriteString(peerID_add + string(";"))
					msg_4.WriteString(string(reason) + string(";"))
					msg_4.WriteString(proposerID + string(";"))
					msg_4_send := msg_4.String()

					// broadcast with PubSub
					pubsub_msg := []byte(msg_4_send)
					go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

					fmt.Printf("\x1b[34m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Println("Your add-proposal was sent to the other peers! Wait for feedback...\n")
					fmt.Printf("\x1b[34m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

					// append to list of own open peer proposals, important to collect votes and manage parallel ones
					myOpenPeerProposals = append(myOpenPeerProposals, string(peerID_add))
					posPeerVotes = append(posPeerVotes, 0)
					negPeerVotes = append(negPeerVotes, 0)
				}

			} // end add peer

			//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

			// remove peer
		case "R":
			fmt.Println("Enter the peerID of the peer you want to remove: ")
			peerID_remove, err := stdReader.ReadString('\n')
			if err != nil {
				log.Fatal(err)
			}
			peerID_remove = strings.Replace(peerID_remove, "\n", "", -1)

			if strings.HasPrefix(peerID_remove, "Qm") == false {
				fmt.Println("ERROR: Invalid PeerID!")
				continue

			} else if peerID_remove == pid_own {
				fmt.Println("ERROR: to remove yourself choose <5> instead!")
				continue

			} else {
				fmt.Printf("You propose to remove PeerID %s.\nProcessing...\n", peerID_remove)

				//Check if peer is really in list/network
				inside_valid := false
				for k := 0; k < len(GlobalPeerList); k++ {
					if GlobalPeerList[k] == peerID_remove {
						inside_valid = true
					}
				}
				if inside_valid == false {
					fmt.Println("Error! The peerID you want to remove is not in the network!")
					continue
				} else {

					// Check if proposer has enough stake to make proposal
					TokenBalance := float64(ownPeerInfo["TokenBalance"].(float64))

					if TokenBalance < requStakeAddRemove {
						fmt.Println("Error! You do not have enough tokens to make a proposal!")
						fmt.Printf("Your token balance is: %v\n", TokenBalance)
						continue

					} else {
						fmt.Println("Everything fine! You have enough tokens to make a proposal!")

						fmt.Println("Please explain why you want to remove this peer:")

						reason, err := stdReader.ReadString('\n')
						if err != nil {
							log.Fatal(err)
						}
						reason = strings.Replace(reason, "\n", "", -1)

						// update AuthorMETRICS: stake deposit and # proposals
						NewTokenBalance := TokenBalance - requStakeAddRemove
						ownPeerInfo["TokenBalance"] = interface{}(NewTokenBalance)

						numberOfProposals := float64(ownPeerInfo["TotalProposals"].(float64))
						NewNumberOfProposals := numberOfProposals + float64(1)
						ownPeerInfo["TotalProposals"] = interface{}(NewNumberOfProposals)

						// write new peerID into message and send.
						var msg_4 strings.Builder
						senderID := ownPeerInfo["PeerID"].(string)
						senderID = senderID + string(";")
						proposerID := senderID
						switchcase := "removeExistingPeerProposal;"
						msg_4.WriteString(senderID)
						msg_4.WriteString(switchcase)
						msg_4.WriteString(peerID_remove + string(";"))
						msg_4.WriteString(string(reason) + string(";"))
						msg_4.WriteString(proposerID + string(";"))
						msg_4_send := msg_4.String()

						// broadcast with PubSub
						pubsub_msg := []byte(msg_4_send)
						go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

						fmt.Printf("\x1b[34m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
						fmt.Printf("Your remove-proposal was sent to the other peers! Wait for feedback...\n")
						fmt.Printf("\x1b[34m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

						// append to list of own open peer proposals, important to collect votes and manage parallel ones
						myOpenPeerProposals = append(myOpenPeerProposals, string(peerID_remove))
						posPeerVotes = append(posPeerVotes, 0)
						negPeerVotes = append(negPeerVotes, 0)

						continue
					}
				}
			} // end remove peer

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
			// add new peer votes
			// positive vote to add peer
		case "add":
			fmt.Println("You agree with the proposal. Send feedback...")

			//update metrics of validator
			ParticipationRateVoting_before := float64(ownPeerInfo["ParticipationVoting"].(float64))
			ParticipationRateVoting_update := ParticipationRateVoting_before + float64(1)
			ownPeerInfo["ParticipationVoting"] = interface{}(ParticipationRateVoting_update)
			validatorReward := float64(requStakeAddRemove)
			TokenBalanceVal := float64(ownPeerInfo["TokenBalance"].(float64))
			UpdateTokenBalanceVal := TokenBalanceVal + validatorReward
			ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalanceVal)

			//read from global variable
			peerID2Add := currentPeerID2AddProposal
			proposer := currentPeerID2AddProposer

			// write vote into msg
			var msg_3 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "myVoteOnAddPeerProposal;"
			msg_3.WriteString(senderID)
			msg_3.WriteString(switchcase)
			msg_3.WriteString(string(peerID2Add) + string(";"))
			msg_3.WriteString(string(proposer) + string(";"))
			msg_3.WriteString("agree")
			msg_3_send := msg_3.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_3_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			// Send and wait for result
			fmt.Println("Vote sent! Waiting for result...")

			// delete finished object from queue: here always the first one in the slice
			copy(openAddPeerAccountProposals[0:], openAddPeerAccountProposals[1:])
			openAddPeerAccountProposals[len(openAddPeerAccountProposals)-1] = ""
			openAddPeerAccountProposals = openAddPeerAccountProposals[:len(openAddPeerAccountProposals)-1]
			//end agree add peer vote

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
			// negative vote to not add peer
		case "not-add":
			fmt.Println("You do not agree with the proposal. Send feedback...")

			//update metrics of validator
			ParticipationRateVoting_before := float64(ownPeerInfo["ParticipationVoting"].(float64))
			ParticipationRateVoting_update := ParticipationRateVoting_before + float64(1)
			ownPeerInfo["ParticipationVoting"] = interface{}(ParticipationRateVoting_update)
			validatorReward := float64(requStakeAddRemove)
			TokenBalanceVal := float64(ownPeerInfo["TokenBalance"].(float64))
			UpdateTokenBalanceVal := TokenBalanceVal + validatorReward
			ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalanceVal)

			//read from global variable
			peerID2Add := currentPeerID2AddProposal
			proposer := currentPeerID2AddProposer

			// write vote into msg
			var msg_3 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "myVoteOnAddPeerProposal;"
			msg_3.WriteString(senderID)
			msg_3.WriteString(switchcase)
			msg_3.WriteString(string(peerID2Add) + string(";"))
			msg_3.WriteString(string(proposer) + string(";"))
			msg_3.WriteString("agree")
			msg_3_send := msg_3.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_3_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			// Send and wait for result
			fmt.Println("Vote sent! Waiting for result...")

			// delete finished object from queue: here always the first one in the slice
			copy(openAddPeerAccountProposals[0:], openAddPeerAccountProposals[1:])
			openAddPeerAccountProposals[len(openAddPeerAccountProposals)-1] = ""
			openAddPeerAccountProposals = openAddPeerAccountProposals[:len(openAddPeerAccountProposals)-1]
		//end disagree add peer vote

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// Here come the remove existing peer votes!
		//positive vote to remove existing peer
		case "remove":
			fmt.Println("You agree with the proposal. Send feedback...")

			//update metrics of validator
			ParticipationRateVoting_before := float64(ownPeerInfo["ParticipationVoting"].(float64))
			ParticipationRateVoting_update := ParticipationRateVoting_before + float64(1)
			ownPeerInfo["ParticipationVoting"] = interface{}(ParticipationRateVoting_update)
			validatorReward := float64(requStakeAddRemove)
			TokenBalanceVal := float64(ownPeerInfo["TokenBalance"].(float64))
			UpdateTokenBalanceVal := TokenBalanceVal + validatorReward
			ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalanceVal)

			//read from global variable
			peerID2remove := currentPeerID2RemoveProposal
			proposer := currentPeerID2RemoveProposer

			// write vote into msg
			var msg_3 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "myVoteOnRemovePeerProposal;"
			msg_3.WriteString(senderID)
			msg_3.WriteString(switchcase)
			msg_3.WriteString(string(peerID2remove) + string(";"))
			msg_3.WriteString(string(proposer) + string(";"))
			msg_3.WriteString("agree")
			msg_3_send := msg_3.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_3_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			// Send and wait for result
			fmt.Println("Vote sent! Waiting for result...")

			// delete finished object from queue: here always the first one in the slice
			copy(openRemovePeerAccountProposals[0:], openRemovePeerAccountProposals[1:])
			openRemovePeerAccountProposals[len(openRemovePeerAccountProposals)-1] = ""
			openRemovePeerAccountProposals = openRemovePeerAccountProposals[:len(openRemovePeerAccountProposals)-1]
			//end agree remove peer vote

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

			//negative vote to remove existing peer
		case "not-remove":
			fmt.Println("You dis-agree with the proposal. Send feedback...")

			//update metrics of validator
			ParticipationRateVoting_before := float64(ownPeerInfo["ParticipationVoting"].(float64))
			ParticipationRateVoting_update := ParticipationRateVoting_before + float64(1)
			ownPeerInfo["ParticipationVoting"] = interface{}(ParticipationRateVoting_update)
			validatorReward := float64(requStakeAddRemove)
			TokenBalanceVal := float64(ownPeerInfo["TokenBalance"].(float64))
			UpdateTokenBalanceVal := TokenBalanceVal + validatorReward
			ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalanceVal)

			//read from global variable
			peerID2remove := currentPeerID2RemoveProposal
			proposer := currentPeerID2RemoveProposer

			// write vote into msg
			var msg_3 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "myVoteOnRemovePeerProposal;"
			msg_3.WriteString(senderID)
			msg_3.WriteString(switchcase)
			msg_3.WriteString(string(peerID2remove) + string(";"))
			msg_3.WriteString(string(proposer) + string(";"))
			msg_3.WriteString("disagree")
			msg_3_send := msg_3.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_3_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			// Send and wait for result
			fmt.Println("Vote sent! Waiting for result...")

			// delete finished object from queue: here always the first one in the slice
			copy(openRemovePeerAccountProposals[0:], openRemovePeerAccountProposals[1:])
			openRemovePeerAccountProposals[len(openRemovePeerAccountProposals)-1] = ""
			openRemovePeerAccountProposals = openRemovePeerAccountProposals[:len(openRemovePeerAccountProposals)-1]
			//end disagree remove peer vote

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

			// single proposal
		case "S":

			jointProposal := false

			fmt.Println("Enter the IPFS hash <Qm...> of the new proposal: ")
			link, err := stdReader.ReadString('\n')
			if err != nil {
				log.Fatal(err)
			}
			// parse incoming link string
			link = strings.Replace(link, "\n", "", -1)

			// Check if link is empty
			if link == "" {
				fmt.Println("ERROR: Empty IPFS hash! ")
				continue

				// Link is not empty but not valid link (IPFS hash has to start with Qm...)
			} else if strings.HasPrefix(link, "Qm") == false {

				fmt.Println("ERROR: Invalid IPFS hash! ")
				continue

				// Link is not empty and valid
			} else {

				fmt.Println("You entered a valid IPFS hash! Processing... ")

				// Define how much stake is necessary:
				fmt.Println("How important do you consider the changes? How much time did you spend? For low press <l>, for middle press <m>, for high press <h>:")
				impact, err := stdReader.ReadString('\n')
				if err != nil {
					log.Fatal(err)
				}
				impact = strings.Replace(impact, "\n", "", -1)

				switch impact {
				case "l":
					requStake = float64(1)
				case "m":
					requStake = float64(2)
				case "h":
					requStake = float64(3)
				}

				fmt.Printf("The required stake are %v tokens.\n", requStake)

				// Check if proposer has enough stake to make proposal
				TokenBalance := float64(ownPeerInfo["TokenBalance"].(float64))

				if TokenBalance < requStake {
					fmt.Println("ERROR! You do not have enough tokens to make a proposal!")
					fmt.Printf("Your token balance is: %v\n", TokenBalance)
					continue

				} else {
					fmt.Println("Everything fine! You have enough tokens to make a proposal!")

					// update AuthorMETRICS: stake deposit and # proposals
					NewTokenBalance := TokenBalance - requStake
					ownPeerInfo["TokenBalance"] = interface{}(NewTokenBalance)

					numberOfProposals := float64(ownPeerInfo["TotalProposals"].(float64))
					NewNumberOfProposals := numberOfProposals + float64(1)
					ownPeerInfo["TotalProposals"] = interface{}(NewNumberOfProposals)

					AuthorMetrics_parsed, err := json.Marshal(ownPeerInfo)
					if err != nil {
						panic(err)
					}

					// create new ProposalMETRICS
					t := time.Now()
					startingTimeProp = append(startingTimeProp, t)
					newProposalMetrics := &ProposalMetrics{requStake, "00:00:00", jointProposal, 0.00, 0.00}
					ProposalMetrics_parsed, err := json.Marshal(newProposalMetrics)
					if err != nil {
						panic(err)
					}

					// update NetworkMETRICS: total network proposals
					networkMetrics := &NetworkMetrics{len(GlobalPeerList)}
					networkMetrics_parsed, err := json.Marshal(networkMetrics)
					if err != nil {
						panic(err)
					}

					// Make new proposal block with new data
					newBlockProposal, err := generateBlock(Blockchain[len(Blockchain)-1], link, string(pid_own), string(AuthorMetrics_parsed), string(ProposalMetrics_parsed), string(networkMetrics_parsed))
					if err != nil {
						log.Println(err)
						continue
					}

					// Check if generated block is valid (not in terms of consensus, but Hashing, Index etc.!)
					if isBlockValid(newBlockProposal, Blockchain[len(Blockchain)-1]) {
						mutex.Lock()
						//Append new proposal to chain - just for transfer - decrypt later
						newBlockchainProposal = append(Blockchain, newBlockProposal)
						mutex.Unlock()
					}

					fmt.Println("New block proposal was successfully created!")

					// Write proposal into own Terminal
					mutex.Lock()
					newBlockProposal_format, err := json.MarshalIndent(newBlockProposal, "", "")
					if err != nil {
						log.Fatal(err)
					}
					fmt.Printf("\x1b[34m%s\x1b[0m> \n", string(newBlockProposal_format))
					mutex.Unlock()

					// make bytes for msg
					newBlockchainProposal_bytes, err := json.Marshal(newBlockchainProposal)
					if err != nil {
						log.Println(err)
					}
					requStake_string := fmt.Sprintf("%f", requStake)

					// Write into variable, send
					var msg_1 strings.Builder
					senderID := ownPeerInfo["PeerID"].(string)
					senderID = senderID + string(";")
					switchcase := "newBlockProposal;"
					msg_1.WriteString(senderID)
					msg_1.WriteString(switchcase)
					msg_1.WriteString(string(newBlockchainProposal_bytes) + string(";"))
					msg_1.WriteString(requStake_string)
					msg_1_send := msg_1.String()

					// broadcast with PubSub
					pubsub_msg := []byte(msg_1_send)
					go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

					// Send and wait for/collect votes
					fmt.Println("Sent to other peers!")

					// append to list of own open block proposals, important to collect votes and manage parallel ones
					myOpenBlockProposals = append(myOpenBlockProposals, string(newBlockProposal_format))
					myRequStakes = append(myRequStakes, requStake)
					posVotes = append(posVotes, 0)
					negVotes = append(negVotes, 0)

				} //enough stake
			} //valid link, end case 1 single proposal

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

			// Here come the single proposal votes!
		case "s-yes":
			fmt.Println("You agree with the proposal. Send feedback...")

			//update metrics of validator
			ParticipationRateVoting_before := float64(ownPeerInfo["ParticipationVoting"].(float64))
			ParticipationRateVoting_update := ParticipationRateVoting_before + float64(1)
			ownPeerInfo["ParticipationVoting"] = interface{}(ParticipationRateVoting_update)
			validatorReward := float64(requStake)
			TokenBalanceVal := float64(ownPeerInfo["TokenBalance"].(float64))
			UpdateTokenBalanceVal := TokenBalanceVal + validatorReward
			ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalanceVal)

			// Write into variable, to be sent and read later
			newBlockchainProposal_bytes, err := json.Marshal(currentBCProposal)
			if err != nil {
				log.Println(err)
			}

			// write vote into variable
			var msg_3 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "myVoteOnNewBlockProposal;"
			msg_3.WriteString(senderID)
			msg_3.WriteString(switchcase)
			msg_3.WriteString(string(newBlockchainProposal_bytes) + string(";"))
			msg_3.WriteString("agree")
			msg_3_send := msg_3.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_3_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			// Send and wait for result
			fmt.Println("Vote sent! Wait for result...")

			//Safe block for verification later: only once
			verifySingleBlockProposals = append(verifySingleBlockProposals, currentBlockProposal)

			//Delete prepared_messages_single (TODO) from lists and other lists
			preparedSent = false
			singleProposalEnoughPrepared = false

			for l := 0; l < len(preparedHASH); l++ {
				if preparedHASH[l] == currentBlockProposal.Hash {
					copy(preparedHASH[l:], preparedHASH[l+1:])
					preparedHASH[len(preparedHASH)-1] = ""
					preparedHASH = preparedHASH[:len(preparedHASH)-1]
					copy(preparedPEERS[l:], preparedPEERS[l+1:])
					preparedPEERS[len(preparedPEERS)-1] = ""
					preparedPEERS = preparedPEERS[:len(preparedPEERS)-1]
					break
				}
			}

			// delete finished object from openNewBlockProposals: here always the first one in the slice
			copy(openNewBlockProposals[0:], openNewBlockProposals[1:])
			openNewBlockProposals[len(openNewBlockProposals)-1] = ""
			openNewBlockProposals = openNewBlockProposals[:len(openNewBlockProposals)-1]

			//end agree single proposal

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

			//disagree on single proposal
		case "s-no":

			fmt.Println("You dis-agree with the proposal. Send feedback...")

			//update metrics of validator
			ParticipationRateVoting_before := float64(ownPeerInfo["ParticipationVoting"].(float64))
			ParticipationRateVoting_update := ParticipationRateVoting_before + float64(1)
			ownPeerInfo["ParticipationVoting"] = interface{}(ParticipationRateVoting_update)
			validatorReward := float64(requStake)
			TokenBalanceVal := float64(ownPeerInfo["TokenBalance"].(float64))
			UpdateTokenBalanceVal := TokenBalanceVal + validatorReward
			ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalanceVal)

			// make bytes for msg
			newBlockchainProposal_bytes, err := json.Marshal(currentBCProposal)
			if err != nil {
				log.Println(err)
			}

			// write into variable and send
			var msg_3 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "myVoteOnNewBlockProposal;"
			msg_3.WriteString(senderID)
			msg_3.WriteString(switchcase)
			msg_3.WriteString(string(newBlockchainProposal_bytes))
			msg_3.WriteString(";disagree")
			msg_3_send := msg_3.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_3_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			// Send and wait for result
			fmt.Println("Vote sent! Wait for result...")

			//Safe block for verification later: only once
			verifySingleBlockProposals = append(verifySingleBlockProposals, currentBlockProposal)

			// delete finished object from openNewBlockProposals
			copy(openNewBlockProposals[0:], openNewBlockProposals[1:])
			openNewBlockProposals[len(openNewBlockProposals)-1] = ""
			openNewBlockProposals = openNewBlockProposals[:len(openNewBlockProposals)-1]

			//Delete prepared_messages_single from lists and other lists
			preparedSent = false
			singleProposalEnoughPrepared = false

			for l := 0; l < len(preparedHASH); l++ {
				if preparedHASH[l] == currentBlockProposal.Hash {
					copy(preparedHASH[l:], preparedHASH[l+1:])
					preparedHASH[len(preparedHASH)-1] = ""
					preparedHASH = preparedHASH[:len(preparedHASH)-1]
					copy(preparedPEERS[l:], preparedPEERS[l+1:])
					preparedPEERS[len(preparedPEERS)-1] = ""
					preparedPEERS = preparedPEERS[:len(preparedPEERS)-1]
					break
				}
			}

			continue //new?!
			// end decline single proposal

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

			// joint proposal
		case "J":

			jointProposal := true

			fmt.Println("How many further peers were involved? Enter the number:")
			numberInvolvedPeers, err := stdReader.ReadString('\n')
			if err != nil {
				log.Fatal(err)
			}
			numberInvolvedPeers = strings.Replace(numberInvolvedPeers, "\n", "", -1)
			nmbInvolvedPeers, err := strconv.Atoi(numberInvolvedPeers)
			if err != nil {
				log.Fatal(err)
			}

			//check if valid input
			if nmbInvolvedPeers < 1 {
				fmt.Println("ERROR: Wrong mode! Choose <1> for single proposal instead!")
				continue

				// ensure that there are enough peers: some must remain for voting!
			} else if len(GlobalPeerList)-nmbInvolvedPeers <= 1 { //1 because of main proposer not counted
				fmt.Println("ERROR: There are not enough other peers to validate your proposal! Make sure at least one other node validates that was not involved in the proposal!")
				continue

			} else {

				var involvedPeersJoint strings.Builder
				involvedPeersJoint.WriteString(string(pid_own) + string(","))

				for i := 0; i < nmbInvolvedPeers; i++ {
					fmt.Printf("Enter the peerID <Qm...> of your supporter number %v:\n", i+1)
					peerIDinvolved, err := stdReader.ReadString('\n')
					if err != nil {
						log.Fatal(err)
					}
					// parse incoming ID
					peerIDinvolved = strings.Replace(peerIDinvolved, "\n", "", -1)

					if strings.HasPrefix(peerIDinvolved, "Qm") == false {
						fmt.Println("ERROR: Invalid PeerID!")
						continue

						// valid ID
					} else {

						//Check if peer is in list
						inside_valid := false
						for k := 0; k < len(GlobalPeerList); k++ {
							if GlobalPeerList[k] == peerIDinvolved {
								inside_valid = true
							}
						}
						if inside_valid == false {
							fmt.Println("ERROR! The peerID you entered is not in the list!")
							continue
						} else {

							if i < nmbInvolvedPeers-1 {
								involvedPeersJoint.WriteString(string(peerIDinvolved) + string(","))
							} else {
								involvedPeersJoint.WriteString(string(peerIDinvolved))
							}
						}
					}
				}
				// create string for involvedPeersJoint: "ID1,ID2,..."
				involvedPeersJointString := involvedPeersJoint.String()

				// now focus on the content
				fmt.Println("Enter the IPFS hash <Qm...> of the new proposal:")
				link, err := stdReader.ReadString('\n')
				if err != nil {
					log.Fatal(err)
				}
				// parse incoming link string
				link = strings.Replace(link, "\n", "", -1)

				// Check if link is empty
				if link == "" {
					fmt.Println("ERROR: Empty IPFS hash! ")
					continue

					// Link is not empty but not valid link (IPFS hash has to start with Qm...)
				} else if strings.HasPrefix(link, "Qm") == false {

					fmt.Println("ERROR: Invalid IPFS hash! ")

					continue

					// Link is not empty and valid
				} else {

					fmt.Println("You entered a valid IPFS hash! Processing... ")

					// Define how much stake is necessary:
					fmt.Println("How important do you consider the changes? How much time did you spend? For low press <l>, for middle press <m>, for high press <h>:")
					impact, err := stdReader.ReadString('\n')
					if err != nil {
						log.Fatal(err)
					}
					impact = strings.Replace(impact, "\n", "", -1)

					// set minimum to enable split between involved peers (at least one token per peer)
					//minimumStake := nmbInvolvedPeers

					switch impact {
					case "l":
						requStakeEachPeer = 0.5 //float64(minimumStake)
					case "m":
						requStakeEachPeer = 1 //2 * float64(minimumStake)
					case "h":
						requStakeEachPeer = 2 //3 * float64(minimumStake)
					}

					totalStakeJoint := requStakeEachPeer * float64(nmbInvolvedPeers+1) //involved peers + main proposer
					fmt.Printf("The required stake for the entire proposal are %v tokens.\n", totalStakeJoint)

					// Split deposits
					//requStakeEachPeer = requStake / float64(nmbInvolvedPeers)
					fmt.Printf("Each peer deposits %v tokens.\n", requStakeEachPeer)

					// Check if main proposer has enough stake to make proposal
					TokenBalance := float64(ownPeerInfo["TokenBalance"].(float64))

					// do this later for every involved peer as well!!!
					if TokenBalance < requStakeEachPeer {
						fmt.Println("ERROR! You do not have enough tokens to make a proposal!")
						fmt.Printf("Your token balance is: %v\n", TokenBalance)
						continue

					} else {
						fmt.Println("Everything fine! You have enough tokens to make a proposal!")

						// update AuthorMETRICS: stake deposit and # proposals
						NewTokenBalance := TokenBalance - requStakeEachPeer
						ownPeerInfo["TokenBalance"] = interface{}(NewTokenBalance)

						numberOfProposals := float64(ownPeerInfo["TotalProposals"].(float64))
						NewNumberOfProposals := numberOfProposals + float64(1)
						ownPeerInfo["TotalProposals"] = interface{}(NewNumberOfProposals)

						AuthorMetrics_parsed, err := json.Marshal(ownPeerInfo)
						if err != nil {
							panic(err)
						}

						// create new ProposalMETRICS
						t := time.Now()
						startingTimeJointProp = append(startingTimeJointProp, t)
						newProposalMetrics := &ProposalMetrics{totalStakeJoint, "00:00:00", jointProposal, 0.00, 0.00} //old: requStake
						ProposalMetrics_parsed, err := json.Marshal(newProposalMetrics)
						if err != nil {
							panic(err)
						}

						// update NetworkMETRICS
						networkMetrics := &NetworkMetrics{len(GlobalPeerList)}
						networkMetrics_parsed, err := json.Marshal(networkMetrics)
						if err != nil {
							panic(err)
						}

						// Make new proposal block with new data
						newBlockProposal, err := generateBlock(Blockchain[len(Blockchain)-1], link, involvedPeersJointString, string(AuthorMetrics_parsed), string(ProposalMetrics_parsed), string(networkMetrics_parsed))
						if err != nil {
							log.Println(err)
							continue
						}

						// Check if generated block is valid (not in terms of consensus, but Hashing, Index etc.!)
						if isBlockValid(newBlockProposal, Blockchain[len(Blockchain)-1]) {
							mutex.Lock()
							//Append new proposal to chain - just for transfer - decrypt later
							newBlockchainProposal = append(Blockchain, newBlockProposal)
							mutex.Unlock()
						}

						fmt.Println("New block proposal was successfully created!")

						// Write proposal into own Terminal
						mutex.Lock()
						newBlockProposal_format, err := json.MarshalIndent(newBlockProposal, "", "")
						if err != nil {
							log.Fatal(err)
						}
						fmt.Printf("\x1b[34m%s\x1b[0m> \n", string(newBlockProposal_format))
						mutex.Unlock()

						// make bytes for msg
						newBlockchainProposal_bytes, err := json.Marshal(newBlockchainProposal)
						if err != nil {
							log.Println(err)
						}

						// append requStakeEachPeer to message as a string
						requStakeEachPeer_string := fmt.Sprintf("%f", requStakeEachPeer)

						// write into variable and send
						var msg_1 strings.Builder
						senderID := ownPeerInfo["PeerID"].(string)
						senderID = senderID + string(";")
						switchcase := "newJointBlockProposal;"
						msg_1.WriteString(senderID)
						msg_1.WriteString(switchcase)
						msg_1.WriteString(string(newBlockchainProposal_bytes) + string(";"))
						msg_1.WriteString(requStakeEachPeer_string)
						msg_1_send := msg_1.String()

						// broadcast with PubSub
						pubsub_msg := []byte(msg_1_send)
						go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

						// Send and wait for/collect votes
						fmt.Println("Sent to involved peers and waiting for pre-vote...")

						// append to list of own open block proposals, important to collect votes and manage parallel ones
						myOpenJointBlockProposals = append(myOpenBlockProposals, string(newBlockProposal_format))
						myOpenJointBlockProposals_bytes = append(myOpenJointBlockProposals_bytes, string(newBlockchainProposal_bytes))
						myRequStakeEachPeer = append(myRequStakeEachPeer, requStakeEachPeer)
						posPreVotesJoint = append(posPreVotesJoint, 0)
						negPreVotesJoint = append(negPreVotesJoint, 0)
					} //enough stake

				} //valid link
			} //end case2: joint proposal

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// accepted joint pre-vote
		case "j-p-yes":
			fmt.Println("You agree (pre-vote) with the joint proposal. Send feedback...")

			//update metrics of involved validators?!
			ParticipationRateVoting_before := float64(ownPeerInfo["ParticipationVoting"].(float64))
			ParticipationRateVoting_update := ParticipationRateVoting_before + float64(1)
			ownPeerInfo["ParticipationVoting"] = interface{}(ParticipationRateVoting_update)
			validatorReward := float64(1) //for pre-vote only one token reward!
			TokenBalanceVal := float64(ownPeerInfo["TokenBalance"].(float64))
			UpdateTokenBalanceVal := TokenBalanceVal + validatorReward
			ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalanceVal)

			// make bytes for msg
			newBlockchainProposal_bytes, err := json.Marshal(currentBCProposal)
			if err != nil {
				log.Println(err)
			}

			// write into variable and send
			var msg_3 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "myJointBlockProposalPreVote;"
			msg_3.WriteString(senderID)
			msg_3.WriteString(switchcase)
			msg_3.WriteString(string(newBlockchainProposal_bytes) + string(";"))
			msg_3.WriteString("agree;")
			msg_3_send := msg_3.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_3_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			// Send and wait for result
			fmt.Println("Vote sent! Wait for result...")

			// delete finished object from openNewJointBlockProposals
			copy(openNewJointBlockProposals[0:], openNewJointBlockProposals[1:])
			openNewJointBlockProposals[len(openNewJointBlockProposals)-1] = ""
			openNewJointBlockProposals = openNewJointBlockProposals[:len(openNewJointBlockProposals)-1]

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

			// declined joint pre-vote
		case "j-p-no":

			fmt.Println("You dis-agree (pre-vote) with the joint proposal. Send feedback...")

			//update metrics of validator
			ParticipationRateVoting_before := float64(ownPeerInfo["ParticipationVoting"].(float64))
			ParticipationRateVoting_update := ParticipationRateVoting_before + float64(1)
			ownPeerInfo["ParticipationVoting"] = interface{}(ParticipationRateVoting_update)
			validatorReward := float64(1) //for pre-vote only one token reward!
			TokenBalanceVal := float64(ownPeerInfo["TokenBalance"].(float64))
			UpdateTokenBalanceVal := TokenBalanceVal + validatorReward
			ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalanceVal)

			// make bytes for msg
			newBlockchainProposal_bytes, err := json.Marshal(currentBCProposal)
			if err != nil {
				log.Println(err)
			}

			// write into variable and send
			var msg_3 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "myJointBlockProposalPreVote;"
			msg_3.WriteString(senderID)
			msg_3.WriteString(switchcase)
			msg_3.WriteString(string(newBlockchainProposal_bytes) + string(";"))
			msg_3.WriteString("disagree;")
			msg_3_send := msg_3.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_3_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			// Send and wait for result
			fmt.Println("Vote sent! Wait for result...")

			// delete finished object from openNewBlockProposals
			copy(openNewJointBlockProposals[0:], openNewJointBlockProposals[1:])
			openNewJointBlockProposals[len(openNewJointBlockProposals)-1] = ""
			openNewJointBlockProposals = openNewJointBlockProposals[:len(openNewJointBlockProposals)-1]

			// show latest valid blockchain
			Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
			if err != nil {
				log.Fatal(err)
			}

			fmt.Println("The latest valid Blockchain is: ")
			fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

			// agree on joint proposal
		case "j-yes":

			fmt.Println("You agree with the joint proposal. Send feedback...")

			//update metrics of validator
			ParticipationRateVoting_before := float64(ownPeerInfo["ParticipationVoting"].(float64))
			ParticipationRateVoting_update := ParticipationRateVoting_before + float64(1)
			ownPeerInfo["ParticipationVoting"] = interface{}(ParticipationRateVoting_update)
			//determine validator reward: from 1 to 3
			var validatorReward float64
			if requStakeEachPeer == 0.5 {
				validatorReward = 1
			} else if requStakeEachPeer == 1 {
				validatorReward = 2
			} else if requStakeEachPeer == 2 {
				validatorReward = 3
			}
			//validatorReward := float64(requStakeEachPeer)
			TokenBalanceVal := float64(ownPeerInfo["TokenBalance"].(float64))
			UpdateTokenBalanceVal := TokenBalanceVal + validatorReward
			ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalanceVal)

			// make bytes for msg
			newBlockchainProposal_bytes, err := json.Marshal(currentBCProposal)
			if err != nil {
				log.Println(err)
			}

			// write vote into variable and send
			var msg_3 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "myVoteOnNewApprovedJointBlockProposal;"
			msg_3.WriteString(senderID)
			msg_3.WriteString(switchcase)
			msg_3.WriteString(string(newBlockchainProposal_bytes) + string(";"))
			msg_3.WriteString("agree")
			msg_3_send := msg_3.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_3_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			// Send and wait for result
			fmt.Println("Vote sent! Wait for result...")

			//Safe block for verification later
			verifyJointBlockProposals = append(verifyJointBlockProposals, currentBlockProposal)

			//Delete prepared_messages_joint from lists and other lists
			preparedSentjoint = false
			jointProposalEnoughPrepared = false

			for l := 0; l < len(preparedHASHjoint); l++ {
				if preparedHASHjoint[l] == currentBlockProposal.Hash {
					copy(preparedHASHjoint[l:], preparedHASHjoint[l+1:])
					preparedHASHjoint[len(preparedHASHjoint)-1] = ""
					preparedHASHjoint = preparedHASHjoint[:len(preparedHASHjoint)-1]
					copy(preparedPEERSjoint[l:], preparedPEERSjoint[l+1:])
					preparedPEERSjoint[len(preparedPEERSjoint)-1] = ""
					preparedPEERSjoint = preparedPEERSjoint[:len(preparedPEERSjoint)-1]
					break
				}
			}

			// delete finished object from openNewBlockProposals: here always the first one in the slice
			copy(openNewApprovedJointBlockProposals[0:], openNewApprovedJointBlockProposals[1:])
			openNewApprovedJointBlockProposals[len(openNewApprovedJointBlockProposals)-1] = ""
			openNewApprovedJointBlockProposals = openNewApprovedJointBlockProposals[:len(openNewApprovedJointBlockProposals)-1]

			//end agree joint proposal

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

			//disagree on joint proposal
		case "j-no":

			fmt.Println("You dis-agree with the joint proposal. Send feedback...")

			//update metrics of validator
			ParticipationRateVoting_before := float64(ownPeerInfo["ParticipationVoting"].(float64))
			ParticipationRateVoting_update := ParticipationRateVoting_before + float64(1)
			ownPeerInfo["ParticipationVoting"] = interface{}(ParticipationRateVoting_update)
			//determine validator reward: from 1 to 3
			var validatorReward float64
			if requStakeEachPeer == 0.5 {
				validatorReward = 1
			} else if requStakeEachPeer == 1 {
				validatorReward = 2
			} else if requStakeEachPeer == 2 {
				validatorReward = 3
			}
			//validatorReward := float64(requStakeEachPeer)
			TokenBalanceVal := float64(ownPeerInfo["TokenBalance"].(float64))
			UpdateTokenBalanceVal := TokenBalanceVal + validatorReward
			ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalanceVal)

			// Write into variable, to be sent and read later
			newBlockchainProposal_bytes, err := json.Marshal(currentBCProposal)
			if err != nil {
				log.Println(err)
			}

			// SIMULATE negative vote
			var msg_3 strings.Builder
			senderID := ownPeerInfo["PeerID"].(string)
			senderID = senderID + string(";")
			switchcase := "myVoteOnNewApprovedJointBlockProposal;"
			msg_3.WriteString(senderID)
			msg_3.WriteString(switchcase)
			msg_3.WriteString(string(newBlockchainProposal_bytes))
			msg_3.WriteString(";disagree")
			msg_3_send := msg_3.String()

			// broadcast with PubSub
			pubsub_msg := []byte(msg_3_send)
			go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

			// Send and wait for result
			fmt.Println("Vote sent! Wait for result...")

			//Safe block for verification later
			verifyJointBlockProposals = append(verifyJointBlockProposals, currentBlockProposal)

			//Delete prepared_messages_single from lists and other lists
			preparedSentjoint = false
			jointProposalEnoughPrepared = false

			for l := 0; l < len(preparedHASHjoint); l++ {
				if preparedHASHjoint[l] == currentBlockProposal.Hash {
					copy(preparedHASHjoint[l:], preparedHASHjoint[l+1:])
					preparedHASHjoint[len(preparedHASHjoint)-1] = ""
					preparedHASHjoint = preparedHASHjoint[:len(preparedHASHjoint)-1]
					copy(preparedPEERSjoint[l:], preparedPEERSjoint[l+1:])
					preparedPEERSjoint[len(preparedPEERSjoint)-1] = ""
					preparedPEERSjoint = preparedPEERSjoint[:len(preparedPEERSjoint)-1]
					break
				}
			}

			// delete finished object from openNewBlockProposals: here always the first one in the slice
			copy(openNewApprovedJointBlockProposals[0:], openNewApprovedJointBlockProposals[1:])
			openNewApprovedJointBlockProposals[len(openNewApprovedJointBlockProposals)-1] = ""
			openNewApprovedJointBlockProposals = openNewApprovedJointBlockProposals[:len(openNewApprovedJointBlockProposals)-1]

			// end decline joint proposal

			//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		} //end of switch proposal types
	} //for loop
} //end handleTerminalInput

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

// handles the buffered io stream
func readWriteProcessData(pubsub_subsrc *pubsub.Subscription, ownPeerInfo map[string]interface{}) {

	//extract own ID to see later if incoming message comes from oneself
	pid_own := ownPeerInfo["PeerID"].(string)

	for {

		// Read incoming string data from pubsub subscription!
		msg, err := pubsub_subsrc.Next(context.Background())
		if err != nil {
			log.Fatal(err)
		}

		//extract the data
		msg_data_bytes := msg.Data
		msg_data_string := string(msg_data_bytes)
		receivedContent := msg_data_string

		// parse incoming data string: sender ; case ; ....rest later
		receivedContent_parsed := strings.Split(msg_data_string, ";")
		sender := receivedContent_parsed[0]
		switchcase := receivedContent_parsed[1]

		// Now handle incoming data depending on the content; switch cases via string:
		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// the received content is the latest valid/global accepted chain of connected peer(s): regulary check if you have the latest chain
		if switchcase == "regularBroadcast" {
			// message does not come from yourself
			if sender != pid_own {
				// read incoming blockchain
				receivedBlockchain := receivedContent_parsed[2]
				// create new blockchain that contains the new string
				regularBroadcastChain := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedBlockchain), &regularBroadcastChain); err != nil {
					log.Fatal(err)
				}
				// Check if new received accepted chain is longer than older one, if yes update your global Blockchain
				mutex.Lock()
				if len(regularBroadcastChain) > len(Blockchain) {
					Blockchain = regularBroadcastChain
					// show latest valid blockchain
					Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
					if err != nil {
						log.Fatal(err)
					}
					fmt.Println("Longer chain received: the latest valid Blockchain is: ")
					fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))
				}
				mutex.Unlock()
			}
		} // end regular broadcast

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		//peers
		if switchcase == "regularPeerUpdate" {
			// message does not come from yourself
			//if sender != pid_own {

			//receive the other local peer list
			receivedPeerList_strg := receivedContent_parsed[2] //"Qm1;Qm2..."
			//receive the other global peer list
			GlobalreceivedPeerList_strg := receivedContent_parsed[3] //"Qm1;Qm2..."
			//fmt.Printf("Liste_received: %v\n", receivedPeerList_strg)

			// parse incoming data string: sender ; case ; ....rest later
			receivedPeerList_strg_parsed := strings.Split(receivedPeerList_strg, ",")
			GlobalreceivedPeerList_strg_parsed := strings.Split(GlobalreceivedPeerList_strg, ",")

			//make slice []string from "string"
			mutex.Lock()
			var receivedPeerList []string
			for z := 0; z < len(receivedPeerList_strg_parsed); z++ {
				receivedPeerList = append(receivedPeerList, receivedPeerList_strg_parsed[z])
			}
			var GlobalreceivedPeerList []string
			for z := 0; z < len(GlobalreceivedPeerList_strg_parsed); z++ {
				GlobalreceivedPeerList = append(GlobalreceivedPeerList, GlobalreceivedPeerList_strg_parsed[z])
			}

			//make a mixed list of all peers
			newList := append(receivedPeerList, myLocalPeers...)
			//delete double entries
			newList = unique(newList)

			//do the same with global list
			newGlobalPeerList := append(GlobalPeerList, newList...)
			newGlobalPeerList = unique(newGlobalPeerList)

			if len(newGlobalPeerList) <= len(GlobalreceivedPeerList) {
				//update
				GlobalPeerList = GlobalreceivedPeerList
			} else {
				//update a
				GlobalPeerList = newGlobalPeerList
			}

			mutex.Unlock()

		} //end Peer Update

		//Invalid peer added: remove!
		if switchcase == "invalidPeerAdd" {
			//check the peer ID
			invalidPeer := receivedContent_parsed[2]
			if pid_own == invalidPeer {
				// remove from network
				fmt.Printf("\x1b[33m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
				fmt.Println("ERROR: Your ID was not confirmed by the other peers! Your connection will be closed...")
				fmt.Printf("\x1b[33m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
				// Unsubscribe from PubSub topic and close stream
				pubsub_subsrc.Cancel()
			}
		}

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// IMPORTANT: messages that come from oneself are ignored as there is no reaction/answer neccessary:
		if sender == pid_own {
			continue

			// messages that come from others
		} else if sender != pid_own {

			// ------CONSENSUS now-------

			// PREPARED MSG single
			if switchcase == "PREPARED" {
				// Check if you already received the same message (via senderID, switchcase and timestamp?)
				if len(openPreparedMsg) > 0 {
					for i := 0; i < len(openPreparedMsg); i++ {
						if strings.Compare(openPreparedMsg[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openPreparedMsg = append(openPreparedMsg, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openPreparedMsg = append(openPreparedMsg, receivedContent)
				}
			}

			// PREPARED MSG joint
			if switchcase == "PREPAREDJOINT" {
				// Check if you already received the same message (via senderID, switchcase and timestamp?)
				if len(openPreparedJointMsg) > 0 {
					for i := 0; i < len(openPreparedJointMsg); i++ {
						if strings.Compare(openPreparedJointMsg[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openPreparedJointMsg = append(openPreparedJointMsg, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openPreparedJointMsg = append(openPreparedJointMsg, receivedContent)
				}
			}

			// PREPARED Fail-MSG: no consensus single
			if switchcase == "PREPAREDFAIL" {
				// Check if you already received the same message (via senderID, switchcase and timestamp?)
				if len(openPreparedFailMsg) > 0 {
					for i := 0; i < len(openPreparedFailMsg); i++ {
						if strings.Compare(openPreparedFailMsg[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openPreparedFailMsg = append(openPreparedFailMsg, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openPreparedFailMsg = append(openPreparedFailMsg, receivedContent)
				}
			}

			// PREPARED Fail-MSG: no consensus joint
			if switchcase == "PREPAREDFAILJOINT" {
				// Check if you already received the same message (via senderID, switchcase and timestamp?)
				if len(openPreparedFailJointMsg) > 0 {
					for i := 0; i < len(openPreparedFailJointMsg); i++ {
						if strings.Compare(openPreparedFailJointMsg[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openPreparedFailJointMsg = append(openPreparedFailJointMsg, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openPreparedFailJointMsg = append(openPreparedFailJointMsg, receivedContent)
				}
			}

			// ------SINGLE now-------

			// single proposal: prepare for vote (receivers)
			if switchcase == "newBlockProposal" {
				// Check if you already received the same message (via senderID, switchcase and timestamp?)
				if len(openNewBlockProposals) > 0 {
					for i := 0; i < len(openNewBlockProposals); i++ {
						if strings.Compare(openNewBlockProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openNewBlockProposals = append(openNewBlockProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openNewBlockProposals = append(openNewBlockProposals, receivedContent)
				}
			}

			// votes for single proposal (proposer): own votes are not collected!
			if switchcase == "myVoteOnNewBlockProposal" {
				if len(openVotesOnNewBlockProposals) > 0 {
					for i := 0; i < len(openVotesOnNewBlockProposals); i++ {
						if strings.Compare(openVotesOnNewBlockProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openVotesOnNewBlockProposals = append(openVotesOnNewBlockProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openVotesOnNewBlockProposals = append(openVotesOnNewBlockProposals, receivedContent)
				}
			}

			// approved single block proposal: final block
			if switchcase == "FinalBlock" {
				if len(FinalBlockNewBlockProposals) > 0 {
					for i := 0; i < len(FinalBlockNewBlockProposals); i++ {
						if strings.Compare(FinalBlockNewBlockProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					FinalBlockNewBlockProposals = append(FinalBlockNewBlockProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					FinalBlockNewBlockProposals = append(FinalBlockNewBlockProposals, receivedContent)
				}
			}

			// approved single block proposal: final block
			if switchcase == "DeclinedProposal" {
				if len(DeclinedNewBlockProposals) > 0 {
					for i := 0; i < len(DeclinedNewBlockProposals); i++ {
						if strings.Compare(DeclinedNewBlockProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					DeclinedNewBlockProposals = append(DeclinedNewBlockProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					DeclinedNewBlockProposals = append(DeclinedNewBlockProposals, receivedContent)
				}
			}

			// ------JOINT now-------

			// joint proposal: pre-votes (only involved peers)
			if switchcase == "newJointBlockProposal" {
				//Check if peer is involved in the proposal, if not ignore
				receivedBlockchainProposal := receivedContent_parsed[2]
				// create new blockchain that contains the new string
				newBlockchainProposal := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedBlockchainProposal), &newBlockchainProposal); err != nil {
					log.Fatal(err)
				}
				// extract the latest (=new unvalidated) block
				proposedBlock := newBlockchainProposal[len(newBlockchainProposal)-1]

				// joint IDs are separated by ","
				involvedProposers_parsed := strings.Split(proposedBlock.Proposer, ",")
				numbInvolvedJointPeers := len(involvedProposers_parsed)

				for j := 0; j < numbInvolvedJointPeers; j++ {
					//peer is involved
					if involvedProposers_parsed[j] == pid_own {
						// Check if you already received the same message (via senderID, switchcase and timestamp?)
						if len(openNewJointBlockProposals) > 0 {
							for i := 0; i < len(openNewJointBlockProposals); i++ {
								if strings.Compare(openNewJointBlockProposals[i], receivedContent) == 0 {
									return //string is already there
								}
							} //no return, not inside: save in queue
							openNewJointBlockProposals = append(openNewJointBlockProposals, receivedContent)

						} else { // openNewBlockProposals was/is empty
							openNewJointBlockProposals = append(openNewJointBlockProposals, receivedContent)
						}
					} //peer is not involved
				} //peer is not involved, for
			} //new joint proposal

			//joint proposal: one peer has not enough tokens
			if switchcase == "JointBlockProposalTokenFail" {
				if len(openNewJointBlockProposalsTokenFails) > 0 {
					for i := 0; i < len(openNewJointBlockProposalsTokenFails); i++ {
						if strings.Compare(openNewJointBlockProposalsTokenFails[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openNewJointBlockProposalsTokenFails = append(openNewJointBlockProposalsTokenFails, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openNewJointBlockProposalsTokenFails = append(openNewJointBlockProposalsTokenFails, receivedContent)
				}
			} //new joint proposal token fail

			// joint proposal: pre-votes (only involved peers)
			if switchcase == "myJointBlockProposalPreVote" {
				if len(openPreVotesOnNewJointBlockProposals) > 0 {
					for i := 0; i < len(openPreVotesOnNewJointBlockProposals); i++ {
						if strings.Compare(openPreVotesOnNewJointBlockProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openPreVotesOnNewJointBlockProposals = append(openPreVotesOnNewJointBlockProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openPreVotesOnNewJointBlockProposals = append(openPreVotesOnNewJointBlockProposals, receivedContent)
				}
			} //jointprevote

			//joint proposal for all after involved peers have pre-voted
			if switchcase == "newApprovedJointBlockProposal" {
				// Check if you already received the same message (via senderID, switchcase and timestamp?)
				if len(openNewApprovedJointBlockProposals) > 0 {
					for i := 0; i < len(openNewApprovedJointBlockProposals); i++ {
						if strings.Compare(openNewApprovedJointBlockProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openNewApprovedJointBlockProposals = append(openNewApprovedJointBlockProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openNewApprovedJointBlockProposals = append(openNewApprovedJointBlockProposals, receivedContent)
				}
			}

			// joint proposal final votes
			if switchcase == "myVoteOnNewApprovedJointBlockProposal" {
				if len(openVotesOnNewApprovedJointBlockProposals) > 0 {
					for i := 0; i < len(openVotesOnNewApprovedJointBlockProposals); i++ {
						if strings.Compare(openVotesOnNewApprovedJointBlockProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openVotesOnNewApprovedJointBlockProposals = append(openVotesOnNewApprovedJointBlockProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openVotesOnNewApprovedJointBlockProposals = append(openVotesOnNewApprovedJointBlockProposals, receivedContent)
				}
			} //end joint proposal final votes

			// joint proposal final block accepted
			if switchcase == "FinalBlockJoint" {
				if len(FinalBlockNewApprovedJointBlockProposals) > 0 {
					for i := 0; i < len(FinalBlockNewApprovedJointBlockProposals); i++ {
						if strings.Compare(FinalBlockNewApprovedJointBlockProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					FinalBlockNewApprovedJointBlockProposals = append(FinalBlockNewApprovedJointBlockProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					FinalBlockNewApprovedJointBlockProposals = append(FinalBlockNewApprovedJointBlockProposals, receivedContent)
				}
			} //end joint proposal final block accepted

			// joint proposal final block declined
			if switchcase == "DeclinedProposalJoint" {
				if len(DeclinedBlockNewApprovedJointBlockProposals) > 0 {
					for i := 0; i < len(DeclinedBlockNewApprovedJointBlockProposals); i++ {
						if strings.Compare(DeclinedBlockNewApprovedJointBlockProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					DeclinedBlockNewApprovedJointBlockProposals = append(DeclinedBlockNewApprovedJointBlockProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					DeclinedBlockNewApprovedJointBlockProposals = append(DeclinedBlockNewApprovedJointBlockProposals, receivedContent)
				}
			} //end joint proposal final block declined

			// ------PEERS now-------

			// remove oneself peer
			if switchcase == "removeOwnPeerAccount" {
				if len(openRemoveOwnPeerAccountProposals) > 0 {
					for i := 0; i < len(openRemoveOwnPeerAccountProposals); i++ {
						if strings.Compare(openRemoveOwnPeerAccountProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openRemoveOwnPeerAccountProposals = append(openRemoveOwnPeerAccountProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openRemoveOwnPeerAccountProposals = append(openRemoveOwnPeerAccountProposals, receivedContent)
				}
			} //end remove myself peer

			// add other peer
			if switchcase == "addNewPeerProposal" {
				if len(openAddPeerAccountProposals) > 0 {
					for i := 0; i < len(openAddPeerAccountProposals); i++ {
						if strings.Compare(openAddPeerAccountProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openAddPeerAccountProposals = append(openAddPeerAccountProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openAddPeerAccountProposals = append(openAddPeerAccountProposals, receivedContent)
				}
			} //end add other peer

			// remove other peer
			if switchcase == "removeExistingPeerProposal" {
				if len(openRemovePeerAccountProposals) > 0 {
					for i := 0; i < len(openRemovePeerAccountProposals); i++ {
						if strings.Compare(openRemovePeerAccountProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openRemovePeerAccountProposals = append(openRemovePeerAccountProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openRemovePeerAccountProposals = append(openRemovePeerAccountProposals, receivedContent)
				}
			} //end remove other peer

			//votes on add new peer
			if switchcase == "myVoteOnAddPeerProposal" {
				if len(openVotesAddPeerAccountProposals) > 0 {
					for i := 0; i < len(openVotesAddPeerAccountProposals); i++ {
						if strings.Compare(openVotesAddPeerAccountProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openVotesAddPeerAccountProposals = append(openVotesAddPeerAccountProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openVotesAddPeerAccountProposals = append(openVotesAddPeerAccountProposals, receivedContent)
				}
			} //end remove other peer

			// add peer accepted
			if switchcase == "FinalAddPeer" {
				if len(openFinalAddPeerAccountProposals) > 0 {
					for i := 0; i < len(openFinalAddPeerAccountProposals); i++ {
						if strings.Compare(openFinalAddPeerAccountProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openFinalAddPeerAccountProposals = append(openFinalAddPeerAccountProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openFinalAddPeerAccountProposals = append(openFinalAddPeerAccountProposals, receivedContent)
				}
			} //end add other peer

			// add peer FinalAddPeerDeclined
			if switchcase == "FinalAddPeerDeclined" {
				if len(openFinalAddPeerAccountProposalsDeclined) > 0 {
					for i := 0; i < len(openFinalAddPeerAccountProposalsDeclined); i++ {
						if strings.Compare(openFinalAddPeerAccountProposalsDeclined[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openFinalAddPeerAccountProposalsDeclined = append(openFinalAddPeerAccountProposalsDeclined, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openFinalAddPeerAccountProposalsDeclined = append(openFinalAddPeerAccountProposalsDeclined, receivedContent)
				}
			} //end add other peer

			// votes for remove other peer
			if switchcase == "myVoteOnRemovePeerProposal" {
				if len(openVotesRemovePeerAccountProposals) > 0 {
					for i := 0; i < len(openVotesRemovePeerAccountProposals); i++ {
						if strings.Compare(openVotesRemovePeerAccountProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openVotesRemovePeerAccountProposals = append(openVotesRemovePeerAccountProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openVotesRemovePeerAccountProposals = append(openVotesRemovePeerAccountProposals, receivedContent)
				}
			} //end remove other peer

			// remove peer accepted
			if switchcase == "FinalRemovalPeer" {
				if len(openFinalRemovePeerAccountProposals) > 0 {
					for i := 0; i < len(openFinalRemovePeerAccountProposals); i++ {
						if strings.Compare(openFinalRemovePeerAccountProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openFinalRemovePeerAccountProposals = append(openFinalRemovePeerAccountProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openFinalRemovePeerAccountProposals = append(openFinalRemovePeerAccountProposals, receivedContent)
				}
			} //end remove other peer

			// remove peer declined
			if switchcase == "FinalRemovalPeerDeclined" {
				if len(openDeclinedRemovePeerAccountProposals) > 0 {
					for i := 0; i < len(openDeclinedRemovePeerAccountProposals); i++ {
						if strings.Compare(openDeclinedRemovePeerAccountProposals[i], receivedContent) == 0 {
							return //string is already there
						}
					} //no return, not inside: save in queue
					openDeclinedRemovePeerAccountProposals = append(openDeclinedRemovePeerAccountProposals, receivedContent)

				} else { // openNewBlockProposals was/is empty
					openDeclinedRemovePeerAccountProposals = append(openDeclinedRemovePeerAccountProposals, receivedContent)
				}
			} //end remove other peer

			//+++++++++
		} //end sender != pid_own

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// DEAL WITH QUEUES: read and process messages one after another from queues

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// PREPARED
		if len(openPreparedMsg) > 0 {
			// read from queue:
			currentContent := openPreparedMsg[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			// new prepared message
			if switchcase == "PREPARED" {
				sender := receivedContent_parsed[0]
				hash := receivedContent_parsed[2]
				proposedBlockAuthor := receivedContent_parsed[3]

				if proposedBlockAuthor != pid_own {

					// add to list if not inside
					mutex.Lock()
					if len(preparedHASH) == 0 {
						preparedHASH = append(preparedHASH, hash)
						preparedPEERS = append(preparedPEERS, sender)

					} else {
						isInside := false
						for j := 0; j < len(preparedHASH); j++ {
							if preparedHASH[j] == hash {
								isInside = true
								//check if sender is already prepared / double msg
								peerInside := false
								preparedPEERS_parsed := strings.Split(preparedPEERS[j], ";")
								for z := 0; z < len(preparedPEERS_parsed); z++ {
									if preparedPEERS_parsed[z] == sender {
										peerInside = true
										break
									}
								}
								//Proposal hash was inside but prepared peer not: add
								if peerInside == false {
									preparedPEERS[j] = preparedPEERS[j] + string(";") + string(sender)
								}
							}
						}
						if isInside == false {
							preparedHASH = append(preparedHASH, hash)
							preparedPEERS = append(preparedPEERS, sender)
						}
					}
					mutex.Unlock()

				} //main proposer ignores prepare messages
			}

			// after check; delete finished object from openVotesOnNewBlockProposals
			copy(openPreparedMsg[0:], openPreparedMsg[1:])
			openPreparedMsg[len(openPreparedMsg)-1] = ""
			openPreparedMsg = openPreparedMsg[:len(openPreparedMsg)-1]

		}

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// PREPARED joint
		if len(openPreparedJointMsg) > 0 {
			// read from queue:
			currentContent := openPreparedJointMsg[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			// new Block proposal comes
			if switchcase == "PREPAREDJOINT" {
				sender := receivedContent_parsed[0]
				hash := receivedContent_parsed[2]
				proposedBlockAuthor := receivedContent_parsed[3]

				if proposedBlockAuthor != pid_own {

					// add to list if not inside
					mutex.Lock()
					if len(preparedHASHjoint) == 0 {
						preparedHASHjoint = append(preparedHASHjoint, hash)
						preparedPEERSjoint = append(preparedPEERSjoint, sender)

					} else {
						isInside := false
						for j := 0; j < len(preparedHASHjoint); j++ {
							if preparedHASHjoint[j] == hash {
								isInside = true
								//check if sender is already prepared / double msg
								peerInside := false
								preparedPEERS_parsed := strings.Split(preparedPEERSjoint[j], ";")
								for z := 0; z < len(preparedPEERS_parsed); z++ {
									if preparedPEERS_parsed[z] == sender {
										peerInside = true
										break
									}
								}
								//Proposal hash was inside but prepared peer not: add
								if peerInside == false {
									preparedPEERSjoint[j] = preparedPEERSjoint[j] + string(";") + string(sender)
								}
							}
						}
						if isInside == false {
							preparedHASHjoint = append(preparedHASHjoint, hash)
							preparedPEERSjoint = append(preparedPEERSjoint, sender)
						}
					}
					mutex.Unlock()

				} //main proposer ignores prepare messages
			}

			// after check; delete finished object from openVotesOnNewBlockProposals
			copy(openPreparedJointMsg[0:], openPreparedJointMsg[1:])
			openPreparedJointMsg[len(openPreparedJointMsg)-1] = ""
			openPreparedJointMsg = openPreparedJointMsg[:len(openPreparedJointMsg)-1]
		}

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// PREPARED Fail single
		if len(openPreparedFailMsg) > 0 {
			// read from queue:
			currentContent := openPreparedFailMsg[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			// For single proposal
			if switchcase == "PREPAREDFAIL" {
				//sender := receivedContent_parsed[0]
				//hash := receivedContent_parsed[2]
				proposedBlockAuthor := receivedContent_parsed[3]
				proposedBlock_format := receivedContent_parsed[4]

				if proposedBlockAuthor == pid_own {
					//fmt.Printf("Prepare consensus for my proposal with hash %s failed! Delete entries...\n", hash)

					// Check if proposal belongs to own proposal; if yes: delete
					for j := 0; j < len(myOpenBlockProposals); j++ {
						if strings.Compare(myOpenBlockProposals[j], string(proposedBlock_format)) == 0 {
							fmt.Println("No consensus reached! Delete proposal...")

							mutex.Lock()

							//Get back stake and adjust number of proposals: myRequStakes[]
							proposalStakeBack := float64(myRequStakes[j])
							TokenBalanceStake := float64(ownPeerInfo["TokenBalance"].(float64))
							UpdateTokenBalance := TokenBalanceStake + proposalStakeBack
							ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalance)

							numberOfProposals := float64(ownPeerInfo["TotalProposals"].(float64))
							NewNumberOfProposals := numberOfProposals - float64(1)
							ownPeerInfo["TotalProposals"] = interface{}(NewNumberOfProposals)

							// delete finished object from myOpenBlockProposals
							copy(myOpenBlockProposals[j:], myOpenBlockProposals[j+1:])
							myOpenBlockProposals[len(myOpenBlockProposals)-1] = ""
							myOpenBlockProposals = myOpenBlockProposals[:len(myOpenBlockProposals)-1]

							// also delete corresponding votes to this proposal!
							copy(posVotes[j:], posVotes[j+1:])
							posVotes[len(posVotes)-1] = 0
							posVotes = posVotes[:len(posVotes)-1]
							copy(negVotes[j:], negVotes[j+1:])
							negVotes[len(negVotes)-1] = 0
							negVotes = negVotes[:len(negVotes)-1]

							// delete requStakes
							copy(myRequStakes[j:], myRequStakes[j+1:])
							myRequStakes[len(myRequStakes)-1] = 0
							myRequStakes = myRequStakes[:len(myRequStakes)-1]

							// delete corresponding time entry for calculation
							copy(startingTimeProp[j:], startingTimeProp[j+1:])
							startingTimeProp[len(startingTimeProp)-1] = time.Now()
							startingTimeProp = startingTimeProp[:len(startingTimeProp)-1]

							mutex.Unlock()
							break
						}
					}
				}
			}

			// delete finished object from openPreparedFailMsg: here always the first one in the slice
			copy(openPreparedFailMsg[0:], openPreparedFailMsg[1:])
			openPreparedFailMsg[len(openPreparedFailMsg)-1] = ""
			openPreparedFailMsg = openPreparedFailMsg[:len(openPreparedFailMsg)-1]

			continue
		}

		// PREPARED Fail joint
		if len(openPreparedFailJointMsg) > 0 {
			// read from queue:
			currentContent := openPreparedFailJointMsg[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			// For joint proposal
			if switchcase == "PREPAREDFAILJOINT" {
				//sender := receivedContent_parsed[0]
				//hash := receivedContent_parsed[2]
				proposedBlockAuthor := receivedContent_parsed[3] //is main author
				proposedBlock_format := receivedContent_parsed[4]

				if proposedBlockAuthor == pid_own {
					//fmt.Printf("Prepare consensus for my proposal with hash %s failed! Delete entries...\n", hash)

					// Check if proposal belongs to own proposal; if yes: delete
					for j := 0; j < len(myOpenApprovedJointBlockProposals); j++ {
						if strings.Compare(myOpenApprovedJointBlockProposals[j], string(proposedBlock_format)) == 0 {
							fmt.Println("No consensus reached! Delete proposal...")

							mutex.Lock()

							//Get back stake and adjust number of proposals: myRequStakes[]
							proposalStakeBack := float64(myRequStakeEachPeer[j])
							TokenBalanceStake := float64(ownPeerInfo["TokenBalance"].(float64))
							UpdateTokenBalance := TokenBalanceStake + proposalStakeBack
							ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalance)

							numberOfProposals := float64(ownPeerInfo["TotalProposals"].(float64))
							NewNumberOfProposals := numberOfProposals - float64(1)
							ownPeerInfo["TotalProposals"] = interface{}(NewNumberOfProposals)

							// delete finished object from myOpenBlockProposals
							copy(myOpenApprovedJointBlockProposals[j:], myOpenApprovedJointBlockProposals[j+1:])
							myOpenApprovedJointBlockProposals[len(myOpenApprovedJointBlockProposals)-1] = ""
							myOpenApprovedJointBlockProposals = myOpenApprovedJointBlockProposals[:len(myOpenApprovedJointBlockProposals)-1]

							// also delete corresponding votes to this proposal!
							copy(posVotesJoint[j:], posVotesJoint[j+1:])
							posVotesJoint[len(posVotesJoint)-1] = 0
							posVotesJoint = posVotesJoint[:len(posVotesJoint)-1]
							copy(negVotesJoint[j:], negVotesJoint[j+1:])
							negVotesJoint[len(negVotesJoint)-1] = 0
							negVotesJoint = negVotesJoint[:len(negVotesJoint)-1]

							// delete requStakes
							copy(myRequStakeEachPeer[j:], myRequStakeEachPeer[j+1:])
							myRequStakeEachPeer[len(myRequStakeEachPeer)-1] = 0
							myRequStakeEachPeer = myRequStakeEachPeer[:len(myRequStakeEachPeer)-1]

							// delete corresponding time entry for calculation
							copy(startingTimeJointProp[j:], startingTimeJointProp[j+1:])
							startingTimeJointProp[len(startingTimeJointProp)-1] = time.Now()
							startingTimeJointProp = startingTimeJointProp[:len(startingTimeJointProp)-1]

							mutex.Unlock()
							break
						}
					}
				}
			}

			// delete finished object from openPreparedFailMsg: here always the first one in the slice
			copy(openPreparedFailJointMsg[0:], openPreparedFailJointMsg[1:])
			openPreparedFailJointMsg[len(openPreparedFailJointMsg)-1] = ""
			openPreparedFailJointMsg = openPreparedFailJointMsg[:len(openPreparedFailJointMsg)-1]

			continue

		}

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// Single block proposals
		if len(openNewBlockProposals) > 0 {
			// read from queue:
			currentContent := openNewBlockProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			// new Block proposal comes
			if switchcase == "newBlockProposal" {

				//read chain and parse
				receivedBlockchainProposal := receivedContent_parsed[2]
				requStake_string := receivedContent_parsed[3]
				requStake_string = strings.Replace(requStake_string, "\n", "", -1)
				requStake, _ = strconv.ParseFloat(requStake_string, 64)

				// create new blockchain that contains the new string
				newBlockchainProposal := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedBlockchainProposal), &newBlockchainProposal); err != nil {
					log.Fatal(err)
				}

				// extract the latest (=new unvalidated) block
				proposedBlock := newBlockchainProposal[len(newBlockchainProposal)-1]

				// check if timeout is already reached
				t_proposal := proposedBlock.Timestamp
				t_proposal_time, err := time.Parse(time.RFC850, t_proposal)
				if err != nil {
					log.Fatal(err)
				}
				t := time.Now()
				t_format := t.Format(time.RFC850)
				t_now_time, err := time.Parse(time.RFC850, t_format)
				if err != nil {
					log.Fatal(err)
				}
				//compare: time diff in seconds
				diff := t_now_time.Sub(t_proposal_time).Seconds()

				// Consensus: make sure all peers received the same proposal and vote on exactly this in the same order!
				if preparedSent == false && diff < proposalTimeOut {
					fmt.Println("Got a new single proposal! Send prepare-message to other peers and wait for consensus...")
					// proposal is uniquely identified by its hash
					var msg_3 strings.Builder
					senderID := ownPeerInfo["PeerID"].(string)
					senderID = senderID + string(";")
					switchcase := "PREPARED;"
					msg_3.WriteString(senderID)
					msg_3.WriteString(switchcase)
					msg_3.WriteString(string(proposedBlock.Hash) + string(";"))
					msg_3.WriteString(string(proposedBlock.Proposer))
					msg_3_send := msg_3.String()

					// broadcast with PubSub:
					pubsub_msg := []byte(msg_3_send)
					go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

					// add to list
					mutex.Lock()
					if len(preparedHASH) == 0 {
						preparedHASH = append(preparedHASH, proposedBlock.Hash)
						preparedPEERS = append(preparedPEERS, pid_own)
					} else {
						isInside := false
						for j := 0; j < len(preparedHASH); j++ {
							if preparedHASH[j] == proposedBlock.Hash {
								isInside = true
							}
						}
						if isInside == false {
							preparedHASH = append(preparedHASH, proposedBlock.Hash)
							preparedPEERS = append(preparedPEERS, pid_own)
						}
					}

					//remember that message was already sent (LOOP makes this neccessary)
					preparedSent = true
					mutex.Unlock()

				} //preparedSent==false and no timeout

				// During valid period: Check if enough "prepared" other peers: if not wait until timeout expires, if yes vote (end timeout)
				if diff < proposalTimeOut && singleProposalEnoughPrepared == false {
					//Check if enough preared messages received
					for k := 0; k < len(preparedHASH); k++ {
						if preparedHASH[k] == proposedBlock.Hash && len(strings.Split(preparedPEERS[k], ";")) >= len(GlobalPeerList)-1 { //-1 because of proposer
							// set variable that allows voting
							singleProposalEnoughPrepared = true
							fmt.Println("Consensus reached!")
							break
						}
					}
				}

				// enough prepared messages within timeframe --> vote
				if singleProposalEnoughPrepared == true {

					// check if timeout is already reached
					t_proposal := proposedBlock.Timestamp
					t_proposal_time, err := time.Parse(time.RFC850, t_proposal)
					if err != nil {
						log.Fatal(err)
					}
					t := time.Now()
					t_format := t.Format(time.RFC850)
					t_now_time, err := time.Parse(time.RFC850, t_format)
					if err != nil {
						log.Fatal(err)
					}
					//compare: time diff in seconds
					diff := t_now_time.Sub(t_proposal_time).Seconds()


					// No timeout reached
					if  diff < votingTimeOut {

						// Print received proposal
						fmt.Printf("New block proposal from peer <%s> received and unpacked: \n", proposedBlock.Proposer)

						//save globally for corresponding vote
						currentBCProposal = newBlockchainProposal
						currentBlockProposal = proposedBlock

						//mutex.Lock()
						proposedBlock_format, err := json.MarshalIndent(proposedBlock, "", "")
						if err != nil {
							log.Fatal(err)
						}
						fmt.Printf("\x1b[31m%s\x1b[0m> \n", string(proposedBlock_format)) //31 rot, 34 blue

						fmt.Printf("Do you agree with the proposed changes?\n If yes: enter <s-yes>; if no: enter <s-no>:\n")

					// Timeout reached
					} else if  diff > votingTimeOut {

						// Write into variable, to be sent and read later
						newBlockchainProposal_bytes, err := json.Marshal(newBlockchainProposal)
						if err != nil {
							log.Println(err)
						}

						// write vote into variable
						var msg_3 strings.Builder
						senderID := ownPeerInfo["PeerID"].(string)
						senderID = senderID + string(";")
						switchcase := "myVoteOnNewBlockProposal;"
						msg_3.WriteString(senderID)
						msg_3.WriteString(switchcase)
						msg_3.WriteString(string(newBlockchainProposal_bytes) + string(";"))
						msg_3.WriteString("timeout")
						msg_3_send := msg_3.String()

						// broadcast with PubSub
						pubsub_msg := []byte(msg_3_send)
						go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

						// Send and wait for result
						fmt.Println("Timeout! Automatic vote sent! Waiting for result...")

						//Safe block for verification later: only once
						verifySingleBlockProposals = append(verifySingleBlockProposals, proposedBlock)

						// delete finished object from queue: here always the first one in the slice
						copy(openNewBlockProposals[0:], openNewBlockProposals[1:])
						openNewBlockProposals[len(openNewBlockProposals)-1] = ""
						openNewBlockProposals = openNewBlockProposals[:len(openNewBlockProposals)-1]
					}
				}

				// not enough prepared messages within timeframe --> delete proposal and notify others (Main proposer)
				if diff > proposalTimeOut && singleProposalEnoughPrepared == false {
					fmt.Println("No consensus reached! Delete proposal...")

					// delete finished object from openNewBlockProposals: here always the first one in the slice
					copy(openNewBlockProposals[0:], openNewBlockProposals[1:])
					openNewBlockProposals[len(openNewBlockProposals)-1] = ""
					openNewBlockProposals = openNewBlockProposals[:len(openNewBlockProposals)-1]

					//Delete prepared_messages_single from lists (if inside)
					preparedSent = false
					singleProposalEnoughPrepared = false//new

					if len(preparedHASH) > 0 { //check if something is in this list, if not ignore
						for l := 0; l < len(preparedHASH); l++ {
							if preparedHASH[l] == proposedBlock.Hash {
								copy(preparedHASH[l:], preparedHASH[l+1:])
								preparedHASH[len(preparedHASH)-1] = ""
								preparedHASH = preparedHASH[:len(preparedHASH)-1]
								copy(preparedPEERS[l:], preparedPEERS[l+1:])
								preparedPEERS[len(preparedPEERS)-1] = ""
								preparedPEERS = preparedPEERS[:len(preparedPEERS)-1]
								break
							}
						}
					}

					//for message, to be compared later
					proposedBlock_format, err := json.MarshalIndent(proposedBlock, "", "")
					if err != nil {
						log.Fatal(err)
					}

					// send message to main proposer to update metrics and delete from list
					var msg_3 strings.Builder
					senderID := ownPeerInfo["PeerID"].(string)
					senderID = senderID + string(";")
					switchcase := "PREPAREDFAIL;"
					msg_3.WriteString(senderID)
					msg_3.WriteString(switchcase)
					msg_3.WriteString(string(proposedBlock.Hash) + string(";"))
					msg_3.WriteString(string(proposedBlock.Proposer + string(";")))
					msg_3.WriteString(string(proposedBlock_format))
					msg_3_send := msg_3.String()

					// broadcast with PubSub:
					pubsub_msg := []byte(msg_3_send)
					go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

					continue
				}

			} //"newBlockProposal"
		} //queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// openVotes for single proposal have arrived
		if len(openVotesOnNewBlockProposals) > 0 {
			// read from queue:
			currentContent := openVotesOnNewBlockProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			if switchcase == "myVoteOnNewBlockProposal" {

				//read incoming chain
				receivedAcceptedBlockchain := receivedContent_parsed[2]

				//extract vote
				peerVote := receivedContent_parsed[3]

				// create new blockchain that contains the new string
				newAcceptedBlockchain := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedAcceptedBlockchain), &newAcceptedBlockchain); err != nil {
					log.Fatal(err)
				}
				// extract the latest (=new unvalidated) block
				proposedBlock := newAcceptedBlockchain[len(newAcceptedBlockchain)-1]

				// modify to string in order to compare it with existing ones
				proposedBlock_format, err := json.MarshalIndent(proposedBlock, "", "")
				if err != nil {
					log.Fatal(err)
				}

				//vote corresponds to one of mine proposals
				if proposedBlock.Proposer == pid_own {

					ownProposal_notInList3 := true

					// collect the incoming votes
					fmt.Println("Collecting and processing votes....")

					// Check if vote belongs to own proposal; if yes: save vote
					for i := 0; i < len(myOpenBlockProposals); i++ {
						if strings.Compare(myOpenBlockProposals[i], string(proposedBlock_format)) == 0 {

							ownProposal_notInList3 = false
							timeout := false
							fmt.Printf("This vote corresponds to one of my open proposals! Save and process vote...\n")
							// save peerVote to corresponding proposal
							if strings.HasPrefix(peerVote, "agree") {
								posVotes[i] = posVotes[i] + 1
							} else if strings.HasPrefix(peerVote, "dis") {
								negVotes[i] = negVotes[i] + 1
							} else if strings.HasPrefix(peerVote, "time") {
								timeout = true
							}

							// after check; delete finished object from openVotesOnNewBlockProposals
							copy(openVotesOnNewBlockProposals[0:], openVotesOnNewBlockProposals[1:])
							openVotesOnNewBlockProposals[len(openVotesOnNewBlockProposals)-1] = ""
							openVotesOnNewBlockProposals = openVotesOnNewBlockProposals[:len(openVotesOnNewBlockProposals)-1]

							//Check if for one of the own proposals a majority of votes is already reached:
							requValidators_float := float64(len(GlobalPeerList) - 1)                // all nodes -1 (proposer) have to vote before result is checked!
							requiredThreshold_abs_float := math.Ceil(2. / 3 * requValidators_float) //2/3 of the required voters for majority
							var requValidators int = int(requValidators_float)
							var requiredThreshold_abs int = int(requiredThreshold_abs_float)

							j := i

							//Check if enough peers have voted
							if (posVotes[j]+negVotes[j] < requValidators) && timeout == false {
								fmt.Println("Not yet enough votes! Wait...")
								continue
							}

							if (posVotes[j]+negVotes[j] < requValidators) && timeout == true {
								fmt.Println("Timeout! Check if majority was reached anyways...")

							}

							//if enough peers have voted, check who won
							if posVotes[j] >= requiredThreshold_abs {
								fmt.Println("Proposal has enough votes and reached a majority: Accepted \n")

								// Reward is double deposit/stake: 3x to get back stake and then double it
								proposalReward := float64(3 * myRequStakes[j]) //vorher: requStake global but then only the latest proposal!
								TokenBalanceStake := float64(ownPeerInfo["TokenBalance"].(float64))
								UpdateTokenBalance := TokenBalanceStake + proposalReward
								ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalance)

								numberOfApprovedProposals := float64(ownPeerInfo["ApprovedProposals"].(float64))
								NewNumberOfApprovedProposals := numberOfApprovedProposals + float64(1)
								ownPeerInfo["ApprovedProposals"] = interface{}(NewNumberOfApprovedProposals)

								AuthorMetrics_parsed, err := json.Marshal(ownPeerInfo)
								if err != nil {
									panic(err)
								}

								// update ProposalMETRICS:
								t0_create := startingTimeProp[j]
								t_diff := time.Since(t0_create)
								t_diff_string := fmt.Sprintf("%v", t_diff)
								participation_abs := float64(posVotes[j] + negVotes[j])
								newProposalMetrics := &ProposalMetrics{myRequStakes[j], t_diff_string, false, float64(posVotes[j]), participation_abs}
								ProposalMetrics_parsed, err := json.Marshal(newProposalMetrics)
								if err != nil {
									panic(err)
								}

								// update NetworkMETRICS: total network proposals
								networkMetrics := &NetworkMetrics{len(GlobalPeerList)}
								networkMetrics_parsed, err := json.Marshal(networkMetrics)
								if err != nil {
									panic(err)
								}

								// Make new proposal block with new-final data
								newAcceptedBlock, err := generateBlock(Blockchain[len(Blockchain)-1], proposedBlock.File, string(pid_own), string(AuthorMetrics_parsed), string(ProposalMetrics_parsed), string(networkMetrics_parsed))
								if err != nil {
									log.Println(err)
									continue
								}

								// Check if generated block is valid (not in terms of consensus, but Hashing, Index etc.!)
								if isBlockValid(newAcceptedBlock, Blockchain[len(Blockchain)-1]) {
									mutex.Lock()
									//Append new proposal to chain - just for transfer - decrypt later
									newAcceptedBlockchain = append(Blockchain, newAcceptedBlock)
									mutex.Unlock()
								}

								fmt.Println("Final accepted block was successfully created!")

								// Write into own Terminal
								mutex.Lock()
								newAcceptedBlock_format, err := json.MarshalIndent(newAcceptedBlock, "", "")
								if err != nil {
									log.Fatal(err)
								}
								fmt.Printf("\x1b[33m%s\x1b[0m> \n", string(newAcceptedBlock_format))
								mutex.Unlock()

								// make bytes for msg
								newAcceptedBlockchain_bytes, err := json.Marshal(newAcceptedBlockchain)
								if err != nil {
									log.Println(err)
								}

								// Write into variable, to be sent and read later
								var msg_8 strings.Builder
								senderID := ownPeerInfo["PeerID"].(string)
								senderID = senderID + string(";")
								switchcase := "FinalBlock;"
								msg_8.WriteString(senderID)
								msg_8.WriteString(switchcase)
								msg_8.WriteString(string(newAcceptedBlockchain_bytes))
								msg_8_send := msg_8.String()

								// broadcast with PubSub
								pubsub_msg := []byte(msg_8_send)
								go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

								// Send and wait for others to append
								fmt.Println("Sent to other peers!")

								// sender can append here directly
								// Check if new received accpeted chain is longer than older one, update global Blockchain
								mutex.Lock()
								if len(newAcceptedBlockchain) > len(Blockchain) {
									Blockchain = newAcceptedBlockchain
									Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
									if err != nil {
										log.Fatal(err)
									}

									fmt.Println("The latest valid Blockchain is: ")
									fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))

								}
								mutex.Unlock()

								// delete finished object from myOpenBlockProposals
								copy(myOpenBlockProposals[j:], myOpenBlockProposals[j+1:])
								myOpenBlockProposals[len(myOpenBlockProposals)-1] = ""
								myOpenBlockProposals = myOpenBlockProposals[:len(myOpenBlockProposals)-1]

								// also delete corresponding votes to this proposal!
								copy(posVotes[j:], posVotes[j+1:])
								posVotes[len(posVotes)-1] = 0
								posVotes = posVotes[:len(posVotes)-1]
								copy(negVotes[j:], negVotes[j+1:])
								negVotes[len(negVotes)-1] = 0
								negVotes = negVotes[:len(negVotes)-1]

								// delete requStakes
								copy(myRequStakes[j:], myRequStakes[j+1:])
								myRequStakes[len(myRequStakes)-1] = 0
								myRequStakes = myRequStakes[:len(myRequStakes)-1]

								// delete corresponding time entry for calculation
								copy(startingTimeProp[j:], startingTimeProp[j+1:])
								startingTimeProp[len(startingTimeProp)-1] = time.Now()
								startingTimeProp = startingTimeProp[:len(startingTimeProp)-1]

								continue

							}

							if negVotes[j] >= requiredThreshold_abs || ((posVotes[j]+negVotes[j] >= requValidators) && negVotes[j] < requiredThreshold_abs) || (timeout == true && (negVotes[j] < requiredThreshold_abs)){
								fmt.Printf("Proposal has enough votes and reached a majority: Declined \n")

								// Reward is double deposit/stake: 3x to get back stake and then double it
								numberOfDeclinedProposals := float64(ownPeerInfo["DeclinedProposals"].(float64))
								NewNumberOfDeclinedProposals := numberOfDeclinedProposals + float64(1)
								ownPeerInfo["DeclinedProposals"] = interface{}(NewNumberOfDeclinedProposals)

								// Write into variable, to be sent and read later
								var msg_8 strings.Builder
								senderID := ownPeerInfo["PeerID"].(string)
								senderID = senderID + string(";")
								switchcase := "DeclinedProposal;"
								msg_8.WriteString(senderID)
								msg_8.WriteString(switchcase)
								msg_8.WriteString(string(proposedBlock.File))
								msg_8_send := msg_8.String()

								// broadcast with PubSub
								pubsub_msg := []byte(msg_8_send)
								go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

								// show latest valid blockchain
								Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
								if err != nil {
									log.Fatal(err)
								}

								fmt.Println("The latest valid Blockchain is: ")
								fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))

								// delete finished object from myOpenBlockProposals
								copy(myOpenBlockProposals[j:], myOpenBlockProposals[j+1:])
								myOpenBlockProposals[len(myOpenBlockProposals)-1] = ""
								myOpenBlockProposals = myOpenBlockProposals[:len(myOpenBlockProposals)-1]

								// also delete corresponding votes to this proposal!
								copy(posVotes[j:], posVotes[j+1:])
								posVotes[len(posVotes)-1] = 0
								posVotes = posVotes[:len(posVotes)-1]
								copy(negVotes[j:], negVotes[j+1:])
								negVotes[len(negVotes)-1] = 0
								negVotes = negVotes[:len(negVotes)-1]

								// delete requStakes
								copy(myRequStakes[j:], myRequStakes[j+1:])
								myRequStakes[len(myRequStakes)-1] = 0
								myRequStakes = myRequStakes[:len(myRequStakes)-1]

								// delete corresponding time entry for calculation
								copy(startingTimeProp[j:], startingTimeProp[j+1:])
								startingTimeProp[len(startingTimeProp)-1] = time.Now()
								startingTimeProp = startingTimeProp[:len(startingTimeProp)-1]

								continue

							} //Declined

						} //belongs to proposal i
					} // for loop own proposals

					// peer received a vote for an already finsihed proposal
					if ownProposal_notInList3 == true {
						// after check; delete finished object from openVotesOnNewBlockProposals
						fmt.Println("Vote cannot be assigned to an open proposal! Delete...")
						copy(openVotesOnNewBlockProposals[0:], openVotesOnNewBlockProposals[1:])
						openVotesOnNewBlockProposals[len(openVotesOnNewBlockProposals)-1] = ""
						openVotesOnNewBlockProposals = openVotesOnNewBlockProposals[:len(openVotesOnNewBlockProposals)-1]
						continue
					}

				} else { //author is not own peer ID = not creator

					// delete finished object from openVotesOnNewBlockProposals
					copy(openVotesOnNewBlockProposals[0:], openVotesOnNewBlockProposals[1:])
					openVotesOnNewBlockProposals[len(openVotesOnNewBlockProposals)-1] = ""
					openVotesOnNewBlockProposals = openVotesOnNewBlockProposals[:len(openVotesOnNewBlockProposals)-1]

				}
			} // switchcase
		} // end openvotes

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		//} else if switchcase == "FinalBlock" : final block received: append
		if len(FinalBlockNewBlockProposals) > 0 {
			// read from queue:
			currentContent := FinalBlockNewBlockProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			if switchcase == "FinalBlock" {

				fmt.Println("Proposal was accepted! Verify and append final block... ")

				receivedAcceptedBlockchain := receivedContent_parsed[2]

				// create new blockchain that contains the new string
				newAcceptedBlockchain := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedAcceptedBlockchain), &newAcceptedBlockchain); err != nil {
					log.Fatal(err)
				}

				// extract the latest block to parse Author/Proposer
				proposedBlock := newAcceptedBlockchain[len(newAcceptedBlockchain)-1]

				if proposedBlock.Proposer != pid_own {

					// Check if is valid: compare if it is in list and hash/link has not changed
					// TODO: make more secure by also checking if it had enough votes.....
					proposer_received := proposedBlock.Proposer
					link_received := proposedBlock.File

					for j := 0; j < len(verifySingleBlockProposals); j++ {
						if verifySingleBlockProposals[j].File == link_received && verifySingleBlockProposals[j].Proposer == proposer_received {
							fmt.Println("New Block verified! Appending...")

							// Check if new received accpeted chain is longer than older one, update global Blockchain
							mutex.Lock()
							if len(newAcceptedBlockchain) > len(Blockchain) {
								Blockchain = newAcceptedBlockchain
								Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
								if err != nil {
									log.Fatal(err)
								}

								fmt.Println("The latest valid Blockchain is: ")
								fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))

							}
							mutex.Unlock()
						}

						//Delete from list
						copy(verifySingleBlockProposals[j:], verifySingleBlockProposals[j+1:])
						verifySingleBlockProposals[len(verifySingleBlockProposals)-1] = proposedBlock //write any block, will be deleted later on
						verifySingleBlockProposals = verifySingleBlockProposals[:len(verifySingleBlockProposals)-1]
						break

					}
				} //not the proposer

				// after check; delete finished object from FinalBlockNewBlockProposals
				copy(FinalBlockNewBlockProposals[0:], FinalBlockNewBlockProposals[1:])
				FinalBlockNewBlockProposals[len(FinalBlockNewBlockProposals)-1] = ""
				FinalBlockNewBlockProposals = FinalBlockNewBlockProposals[:len(FinalBlockNewBlockProposals)-1]

				continue

			} //end finalBlock
		} //end queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// declined block received: update metrics
		if len(DeclinedNewBlockProposals) > 0 {
			// read from queue:
			currentContent := DeclinedNewBlockProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]
			link_received := receivedContent_parsed[2]

			if switchcase == "DeclinedProposal" {

				fmt.Println("Proposal was declined! Update metrics...")

				if sender != pid_own {

					//delete from list
					for j := 0; j < len(verifySingleBlockProposals); j++ {
						if verifySingleBlockProposals[j].File == link_received {
							//fmt.Println("Delete corresponding proposal from verification list...")

							//Delete from list
							randomBlock := verifySingleBlockProposals[j]
							copy(verifySingleBlockProposals[j:], verifySingleBlockProposals[j+1:])
							verifySingleBlockProposals[len(verifySingleBlockProposals)-1] = randomBlock //write any block, will be deleted later on
							verifySingleBlockProposals = verifySingleBlockProposals[:len(verifySingleBlockProposals)-1]
							break
						}
					}

					// show latest valid blockchain
					Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
					if err != nil {
						log.Fatal(err)
					}

					fmt.Println("The latest valid Blockchain is: ")
					fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))
				} //sender not own peerid

				// after check; delete finished object from DeclinedNewBlockProposals
				copy(DeclinedNewBlockProposals[0:], DeclinedNewBlockProposals[1:])
				DeclinedNewBlockProposals[len(DeclinedNewBlockProposals)-1] = ""
				DeclinedNewBlockProposals = DeclinedNewBlockProposals[:len(DeclinedNewBlockProposals)-1]

				continue

			} // end DeclinedProposal
		} //queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
		//JOINT Now
		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// joint proposal: peer is involved
		if len(openNewJointBlockProposals) > 0 {
			// read from queue:
			currentContent := openNewJointBlockProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			if switchcase == "newJointBlockProposal" {

				//read chain
				receivedBlockchainProposal := receivedContent_parsed[2]
				requStakeEachPeer_string := receivedContent_parsed[3]
				requStakeEachPeer_string = strings.Replace(requStakeEachPeer_string, "\n", "", -1)
				requStakeEachPeer, _ = strconv.ParseFloat(requStakeEachPeer_string, 64)

				// create new blockchain that contains the new string
				newBlockchainProposal := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedBlockchainProposal), &newBlockchainProposal); err != nil {
					log.Fatal(err)
				}

				// extract the latest (=new unvalidated) block
				proposedBlock := newBlockchainProposal[len(newBlockchainProposal)-1]

				// joint IDs are separated by ";": parse and check individually, adjust stake/deposit of involved peers; let them disagree if wrong!!
				involvedProposers_parsed := strings.Split(proposedBlock.Proposer, ",")

				fmt.Println("New joint block proposal received and unpacked!")
				fmt.Printf("Peer ID <%s> said you are involved in this joint proposal:\n", sender)
				fmt.Println("The following peers are involved: %s\n", involvedProposers_parsed)

				// show
				proposedBlock_format, err := json.MarshalIndent(proposedBlock, "", "")
				if err != nil {
					log.Fatal(err)
				}
				fmt.Printf("\x1b[31m%s\x1b[0m> \n", string(proposedBlock_format)) //31 rot, 34 blue

				fmt.Printf("Checking requirements...")

				// Check if the involved proposer has enough stake to make proposal
				TokenBalance := float64(ownPeerInfo["TokenBalance"].(float64))

				if TokenBalance < requStakeEachPeer {
					fmt.Println("Error! You do not have enough tokens to participate in making this joint proposal!")
					fmt.Printf("Your token balance is: %v\n", TokenBalance)

					// make bytes for msg
					newJointBlockProposal_bytes, err := json.Marshal(newBlockchainProposal)
					if err != nil {
						log.Println(err)
					}

					// Write stake for main proposer to update
					requStakeEachPeer_string := fmt.Sprintf("%f", requStakeEachPeer)

					// Write into variable, to be sent and read later
					var msg_8 strings.Builder
					senderID := ownPeerInfo["PeerID"].(string)
					senderID = senderID + string(";")
					switchcase := "JointBlockProposalTokenFail;"
					msg_8.WriteString(senderID)
					msg_8.WriteString(switchcase)
					msg_8.WriteString(string(newJointBlockProposal_bytes) + string(";"))
					msg_8.WriteString(requStakeEachPeer_string + string(";"))
					msg_8.WriteString(sender) //the receiver of this message is the main proposer of this joint proposal
					msg_8_send := msg_8.String()

					// broadcast with PubSub
					pubsub_msg := []byte(msg_8_send)
					go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

					// delete finished object from myOpenJointBlockProposals
					copy(openNewJointBlockProposals[0:], openNewJointBlockProposals[1:])
					openNewJointBlockProposals[len(openNewJointBlockProposals)-1] = ""
					openNewJointBlockProposals = openNewJointBlockProposals[:len(openNewJointBlockProposals)-1]

					// show latest valid blockchain
					Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
					if err != nil {
						log.Fatal(err)
					}

					fmt.Println("The latest valid Blockchain is: ")
					fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))

					continue

				} else {
					fmt.Println("Everything fine! You have enough tokens to participate in making this joint proposal!")

					//save globally for corresponding vote
					currentBCProposal = newBlockchainProposal
					currentBlockProposal = proposedBlock

					fmt.Printf("Are you really involved in this joint proposal? Do you agree with the proposed changes?\n")
					fmt.Println("If yes: enter <j-p-yes>; if no: enter <j-p-no>:")
					//handle this in other goroutine! --> punish sender if involved peer declines!

				} //enough stake to make this proposal
			} //new joint block proposal
		} //joint proposal in queue, peer is involved, end

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// joint proposal failed: one peer has not enough token
		if len(openNewJointBlockProposalsTokenFails) > 0 {
			// read from queue:
			currentContent := openNewJointBlockProposalsTokenFails[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			if switchcase == "JointBlockProposalTokenFail" {

				// read in
				guilty_peer := receivedContent_parsed[0]
				requStakeEachPeer_string := receivedContent_parsed[3]
				main_author := receivedContent_parsed[4] //the receiver of this message is the main proposer of this joint proposal
				main_author = strings.Replace(main_author, "\n", "", -1)
				requStakeEachPeer_string = strings.Replace(requStakeEachPeer_string, "\n", "", -1)
				requStakeEachPeer, _ = strconv.ParseFloat(requStakeEachPeer_string, 64)

				// extract further Content
				receivedjointBlockchainProposal := receivedContent_parsed[2]

				// create new blockchain that contains the new string
				newreceivedjointBlockchainProposal := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedjointBlockchainProposal), &newreceivedjointBlockchainProposal); err != nil {
					log.Fatal(err)
				}

				// extract the latest (=new unvalidated) block
				proposedBlock := newreceivedjointBlockchainProposal[len(newreceivedjointBlockchainProposal)-1]

				// modify to string in order to compare it with existing ones
				proposedBlock_format, err := json.MarshalIndent(proposedBlock, "", "")
				if err != nil {
					log.Fatal(err)
				}

				//check if ownpeer id was responsible for this joint proposal
				if main_author == pid_own {
					fmt.Printf("ERROR: The involved peer <%s> had not enough stake! Delete proposal...\n", guilty_peer)

					// main proposer gets hiw stake back as it is not his fault that involved peers do not have enough token
					TokenBalanceStake := float64(ownPeerInfo["TokenBalance"].(float64))
					NewTokenBalance := TokenBalanceStake + requStakeEachPeer
					ownPeerInfo["TokenBalance"] = interface{}(NewTokenBalance)

					// delete the corresponding joint proposal from lists
					for j := 0; j < len(myOpenJointBlockProposals); j++ {
						if strings.Compare(myOpenJointBlockProposals[j], string(proposedBlock_format)) == 0 {

							copy(myOpenJointBlockProposals[j:], myOpenJointBlockProposals[j+1:])
							myOpenJointBlockProposals[len(myOpenJointBlockProposals)-1] = ""
							myOpenJointBlockProposals = myOpenJointBlockProposals[:len(myOpenJointBlockProposals)-1]

							copy(myOpenJointBlockProposals_bytes[j:], myOpenJointBlockProposals_bytes[j+1:])
							myOpenJointBlockProposals_bytes[len(myOpenJointBlockProposals_bytes)-1] = ""
							myOpenJointBlockProposals_bytes = myOpenJointBlockProposals_bytes[:len(myOpenJointBlockProposals_bytes)-1]

							// also delete corresponding pre-votes to this proposal!
							copy(posPreVotesJoint[j:], posPreVotesJoint[j+1:])
							posPreVotesJoint[len(posPreVotesJoint)-1] = 0
							posPreVotesJoint = posPreVotesJoint[:len(posPreVotesJoint)-1]
							copy(negPreVotesJoint[j:], negPreVotesJoint[j+1:])
							negPreVotesJoint[len(negPreVotesJoint)-1] = 0
							negPreVotesJoint = negPreVotesJoint[:len(negPreVotesJoint)-1]

							//delete the requStakes entry
							copy(myRequStakeEachPeer[j:], myRequStakeEachPeer[j+1:])
							myRequStakeEachPeer[len(myRequStakeEachPeer)-1] = 0
							myRequStakeEachPeer = myRequStakeEachPeer[:len(myRequStakeEachPeer)-1]
						}
					}

					// show latest valid blockchain
					Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
					if err != nil {
						log.Fatal(err)
					}

					fmt.Println("The latest valid Blockchain is: ")
					fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))
				} //main Author

				//Delete from queue after finishing
				copy(openNewJointBlockProposalsTokenFails[0:], openNewJointBlockProposalsTokenFails[1:])
				openNewJointBlockProposalsTokenFails[len(openNewJointBlockProposalsTokenFails)-1] = ""
				openNewJointBlockProposalsTokenFails = openNewJointBlockProposalsTokenFails[:len(openNewJointBlockProposalsTokenFails)-1]

			} //end joint block proposal token fail of involved peer
		} //queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		//Prevote collection of joint proposal: process the prevotes of involved peers
		if len(openPreVotesOnNewJointBlockProposals) > 0 {
			// read from queue:
			currentContent := openPreVotesOnNewJointBlockProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			if switchcase == "myJointBlockProposalPreVote" {

				// extract vote
				peerPreVote := receivedContent_parsed[3]
				// extract further Content
				receivedjointBlockchainProposal := receivedContent_parsed[2]

				// create new blockchain that contains the new string
				newreceivedjointBlockchainProposal := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedjointBlockchainProposal), &newreceivedjointBlockchainProposal); err != nil {
					log.Fatal(err)
				}

				// extract the latest (=new unvalidated) block
				proposedBlock := newreceivedjointBlockchainProposal[len(newreceivedjointBlockchainProposal)-1]

				// modify to string in order to compare it with existing ones
				proposedBlock_format, err := json.MarshalIndent(proposedBlock, "", "")
				if err != nil {
					log.Fatal(err)
				}

				// more than one proposer: extract them
				involvedProposers_parsed := strings.Split(proposedBlock.Proposer, ",")

				//main proposer is first peer in list: main proposer handles collecting of votes
				if involvedProposers_parsed[0] == pid_own {

					ownProposal_notInList := true

					// Check if vote belongs to own proposal; if yes: save vote
					for i := 0; i < len(myOpenJointBlockProposals); i++ {
						if strings.Compare(myOpenJointBlockProposals[i], string(proposedBlock_format)) == 0 {
							ownProposal_notInList = false
							fmt.Printf("This vote corresponds to one of my open proposals! Save and process vote...\n")
							// save peerVote to corresponding proposal
							if strings.HasPrefix(peerPreVote, "agree") {
								posPreVotesJoint[i] = posPreVotesJoint[i] + 1
							} else if strings.HasPrefix(peerPreVote, "dis") {
								negPreVotesJoint[i] = negPreVotesJoint[i] + 1
							}

							// after check; delete finished object from openPreVotesOnNewJointBlockProposals
							copy(openPreVotesOnNewJointBlockProposals[0:], openPreVotesOnNewJointBlockProposals[1:])
							openPreVotesOnNewJointBlockProposals[len(openPreVotesOnNewJointBlockProposals)-1] = ""
							openPreVotesOnNewJointBlockProposals = openPreVotesOnNewJointBlockProposals[:len(openPreVotesOnNewJointBlockProposals)-1]
							// Now this vote has been processed and deleted from the list

							j := i

							// Voting: different for each proposal! check for the current one (-main proposer who does not vote)
							requValidatorsJointPreVote := len(involvedProposers_parsed) - 1
							requiredThreshold_absJointPreVote := requValidatorsJointPreVote

							//Check if enough peers have voted
							if posPreVotesJoint[j]+negPreVotesJoint[j] < requValidatorsJointPreVote {
								fmt.Println("Not yet enough pre-votes! Wait...")
								continue
							}

							//if enough peers have voted, check who won
							if posPreVotesJoint[j] >= requiredThreshold_absJointPreVote {
								fmt.Printf("Proposal has enough pre-votes and reached a majority: Accepted \n")

								//newBlockchainProposal_bytes, err := json.Marshal(myOpenJointBlockProposals[j])
								newBlockchainProposal_bytes := myOpenJointBlockProposals_bytes[j] //string --> Marshal

								// append requStakeEachPeer to message as a string
								requStakeEachPeer_string := fmt.Sprintf("%f", myRequStakeEachPeer[j])

								//broadcast joint proposal to all for voting
								var msg_1 strings.Builder
								senderID := ownPeerInfo["PeerID"].(string)
								senderID = senderID + string(";")
								switchcase := "newApprovedJointBlockProposal;"
								msg_1.WriteString(senderID)
								msg_1.WriteString(switchcase)
								//msg_1.WriteString(string(newBlockchainProposal_bytes) + string(";"))
								msg_1.WriteString(newBlockchainProposal_bytes + string(";"))
								msg_1.WriteString(requStakeEachPeer_string)
								msg_1_send := msg_1.String()

								// broadcast with PubSub
								pubsub_msg := []byte(msg_1_send)
								go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

								// append to list of own open block proposals, important to collect votes and manage parallel ones
								myOpenApprovedJointBlockProposals = append(myOpenApprovedJointBlockProposals, string(myOpenJointBlockProposals[j]))
								posVotesJoint = append(posVotesJoint, 0)
								negVotesJoint = append(negVotesJoint, 0)

								// delete finished object from myOpenBlockProposals
								copy(myOpenJointBlockProposals[j:], myOpenJointBlockProposals[j+1:])
								myOpenJointBlockProposals[len(myOpenJointBlockProposals)-1] = ""
								myOpenJointBlockProposals = myOpenJointBlockProposals[:len(myOpenJointBlockProposals)-1]

								copy(myOpenJointBlockProposals_bytes[j:], myOpenJointBlockProposals_bytes[j+1:])
								myOpenJointBlockProposals_bytes[len(myOpenJointBlockProposals_bytes)-1] = ""
								myOpenJointBlockProposals_bytes = myOpenJointBlockProposals_bytes[:len(myOpenJointBlockProposals_bytes)-1]

								// delete corresponding prevotes to this proposal!
								copy(posPreVotesJoint[j:], posPreVotesJoint[j+1:])
								posPreVotesJoint[len(posPreVotesJoint)-1] = 0
								posPreVotesJoint = posPreVotesJoint[:len(posPreVotesJoint)-1]
								copy(negPreVotesJoint[j:], negPreVotesJoint[j+1:])
								negPreVotesJoint[len(negPreVotesJoint)-1] = 0
								negPreVotesJoint = negPreVotesJoint[:len(negPreVotesJoint)-1]

								// delete NOT the requStakes entry as needed after positive pre-vote
								// delete NOT time entry as needed after positive pre-vote

								// Send and wait for others to vote
								fmt.Println("Send to other peers and wait for votes...")

								continue

							} //pre-vote accepted

							if negPreVotesJoint[j] >= requiredThreshold_absJointPreVote || ((posPreVotesJoint[j]+negPreVotesJoint[j] >= requValidatorsJointPreVote) && negPreVotesJoint[j] < requiredThreshold_absJointPreVote) {

								fmt.Printf("Proposal has enough pre-votes and reached a majority: Declined \n")

								// Punish main proposer as one of its involved peers did not accept the joint proposal
								numberOfDeclinedProposals := float64(ownPeerInfo["DeclinedProposals"].(float64))
								NewNumberOfDeclinedProposals := numberOfDeclinedProposals + float64(1)
								ownPeerInfo["DeclinedProposals"] = interface{}(NewNumberOfDeclinedProposals)

								// delete finished object from myOpenBlockProposals
								copy(myOpenJointBlockProposals[j:], myOpenJointBlockProposals[j+1:])
								myOpenJointBlockProposals[len(myOpenJointBlockProposals)-1] = ""
								myOpenJointBlockProposals = myOpenJointBlockProposals[:len(myOpenJointBlockProposals)-1]

								copy(myOpenJointBlockProposals_bytes[j:], myOpenJointBlockProposals_bytes[j+1:])
								myOpenJointBlockProposals_bytes[len(myOpenJointBlockProposals_bytes)-1] = ""
								myOpenJointBlockProposals_bytes = myOpenJointBlockProposals_bytes[:len(myOpenJointBlockProposals_bytes)-1]

								// also delete corresponding pre-votes to this proposal!
								copy(posPreVotesJoint[j:], posPreVotesJoint[j+1:])
								posPreVotesJoint[len(posPreVotesJoint)-1] = 0
								posPreVotesJoint = posPreVotesJoint[:len(posPreVotesJoint)-1]
								copy(negPreVotesJoint[j:], negPreVotesJoint[j+1:])
								negPreVotesJoint[len(negPreVotesJoint)-1] = 0
								negPreVotesJoint = negPreVotesJoint[:len(negPreVotesJoint)-1]

								//delete the requStakes entry
								copy(myRequStakeEachPeer[j:], myRequStakeEachPeer[j+1:])
								myRequStakeEachPeer[len(myRequStakeEachPeer)-1] = 0
								myRequStakeEachPeer = myRequStakeEachPeer[:len(myRequStakeEachPeer)-1]

								// delete corresponding time entry for calculation
								copy(startingTimeJointProp[j:], startingTimeJointProp[j+1:])
								startingTimeJointProp[len(startingTimeJointProp)-1] = time.Now()
								startingTimeJointProp = startingTimeJointProp[:len(startingTimeJointProp)-1]

								// show latest valid blockchain
								Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
								if err != nil {
									log.Fatal(err)
								}

								fmt.Println("The latest valid Blockchain is: ")
								fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))

								//back to welcome
								continue
							} //pre-vote declined
						} //i
					} //for list

					// peer received a vote for an already finsihed proposal
					if ownProposal_notInList == true {
						// after check; delete finished object from openPreVotesOnNewJointBlockProposals
						copy(openPreVotesOnNewJointBlockProposals[0:], openPreVotesOnNewJointBlockProposals[1:])
						openPreVotesOnNewJointBlockProposals[len(openPreVotesOnNewJointBlockProposals)-1] = ""
						openPreVotesOnNewJointBlockProposals = openPreVotesOnNewJointBlockProposals[:len(openPreVotesOnNewJointBlockProposals)-1]
					}
				} else { //author is not own peer ID = not creator

					// after check; delete finished object from openPreVotesOnNewJointBlockProposals
					copy(openPreVotesOnNewJointBlockProposals[0:], openPreVotesOnNewJointBlockProposals[1:])
					openPreVotesOnNewJointBlockProposals[len(openPreVotesOnNewJointBlockProposals)-1] = ""
					openPreVotesOnNewJointBlockProposals = openPreVotesOnNewJointBlockProposals[:len(openPreVotesOnNewJointBlockProposals)-1]

				} //author

			} // end switchcase
		} // open votes queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// voting for joint proposal (after involved peers agreed in pre-voting)
		if len(openNewApprovedJointBlockProposals) > 0 {
			// read from queue:
			currentContent := openNewApprovedJointBlockProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			if switchcase == "newApprovedJointBlockProposal" {

				//parse incoming message
				receivedjointBlockchainProposal := receivedContent_parsed[2]
				sender := receivedContent_parsed[0]
				requStakeEachPeer_string := receivedContent_parsed[3]
				requStakeEachPeer_string = strings.Replace(requStakeEachPeer_string, "\n", "", -1)
				requStakeEachPeer, _ = strconv.ParseFloat(requStakeEachPeer_string, 64)

				// create new blockchain that contains the new string
				newreceivedjointBlockchainProposal := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedjointBlockchainProposal), &newreceivedjointBlockchainProposal); err != nil {
					log.Fatal(err)
				}
				// extract the latest (=new unvalidated) block
				proposedBlock := newreceivedjointBlockchainProposal[len(newreceivedjointBlockchainProposal)-1]

				// check if timeout is already reached
				t_proposal := proposedBlock.Timestamp
				t_proposal_time, err := time.Parse(time.RFC850, t_proposal)
				if err != nil {
					log.Fatal(err)
				}
				t := time.Now()
				t_format := t.Format(time.RFC850)
				t_now_time, err := time.Parse(time.RFC850, t_format)
				if err != nil {
					log.Fatal(err)
				}
				//compare: time diff in seconds
				diff := t_now_time.Sub(t_proposal_time).Seconds()

				//extract main proposer as he handles the consensus
				proposers := strings.Split(proposedBlock.Proposer, ",")
				mainProposer := proposers[0]

				// Consensus: make sure all peers received the same proposal and vote on exactly this in the same order!
				if preparedSentjoint == false && diff < proposalTimeOut {
					fmt.Println("Got a new joint proposal. Send prepare-message to other peers and wait for consensus...")
					// proposal is uniquely identified by its hash
					var msg_3 strings.Builder
					senderID := ownPeerInfo["PeerID"].(string)
					senderID = senderID + string(";")
					switchcase := "PREPAREDJOINT;"
					msg_3.WriteString(senderID)
					msg_3.WriteString(switchcase)
					msg_3.WriteString(string(proposedBlock.Hash) + string(";"))
					msg_3.WriteString(string(mainProposer)) //only main proposer
					msg_3_send := msg_3.String()

					// broadcast with PubSub:
					pubsub_msg := []byte(msg_3_send)
					go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

					// add to list
					if len(preparedHASHjoint) == 0 {
						preparedHASHjoint = append(preparedHASHjoint, proposedBlock.Hash)
						preparedPEERSjoint = append(preparedPEERSjoint, pid_own)
					} else {
						isInside := false
						for j := 0; j < len(preparedHASHjoint); j++ {
							if preparedHASHjoint[j] == proposedBlock.Hash {
								isInside = true
							}
						}
						if isInside == false {
							preparedHASHjoint = append(preparedHASHjoint, proposedBlock.Hash)
							preparedPEERSjoint = append(preparedPEERSjoint, pid_own)
						}
					}

					//remember that message was already sent (LOOP makes this neccessary)
					preparedSentjoint = true

				} //preparedSent==false and no timeout

				// During valid period: Check if enough "prepared" other peers: if not wait until timeout expires, if yes vote (end timeout)
				if diff < proposalTimeOut && jointProposalEnoughPrepared == false {
					//Check if enough preared messages received
					for k := 0; k < len(preparedHASHjoint); k++ {
						if preparedHASHjoint[k] == proposedBlock.Hash && len(strings.Split(preparedPEERSjoint[k], ";")) >= len(GlobalPeerList)-1 { //-1 because of proposer
							// set variable that allows voting
							jointProposalEnoughPrepared = true
							fmt.Println("Consensus reached!")
							break
						}
					}
				}

				// enough prepared messages within timeframe --> vote
				if jointProposalEnoughPrepared == true {

					// more than one proposer
					involvedProposers_parsed := strings.Split(proposedBlock.Proposer, ",")
					numbInvolvedJointPeers := len(involvedProposers_parsed)

					flag_involved := false

					for j := 0; j < numbInvolvedJointPeers; j++ {
						//peer is involved in this proposal
						if involvedProposers_parsed[j] == pid_own {

							flag_involved = true
							//involved but not the main proposer
							if sender != pid_own {
								// the involved peers get notified
								fmt.Println("Your joint block proposal is in the voting process now...")

								// update AuthorMETRICS of involved peers: -stake from involved peers (in the pre-vote not done (only main proposer) as not sure if accepted by all; hence here)
								TokenBalance := float64(ownPeerInfo["TokenBalance"].(float64))
								NewTokenBalance := TokenBalance - requStakeEachPeer
								ownPeerInfo["TokenBalance"] = interface{}(NewTokenBalance)

								numberOfProposals := float64(ownPeerInfo["TotalProposals"].(float64))
								NewNumberOfProposals := numberOfProposals + float64(1)
								ownPeerInfo["TotalProposals"] = interface{}(NewNumberOfProposals)

								//Delete prepared_messages_single from lists (if inside)
								preparedSentjoint = false
								jointProposalEnoughPrepared = false

								if len(preparedHASHjoint) > 0 { //check if something is in this list, if not ignore
									for l := 0; l < len(preparedHASHjoint); l++ {
										if preparedHASHjoint[l] == proposedBlock.Hash {
											copy(preparedHASHjoint[l:], preparedHASHjoint[l+1:])
											preparedHASHjoint[len(preparedHASHjoint)-1] = ""
											preparedHASHjoint = preparedHASHjoint[:len(preparedHASHjoint)-1]
											copy(preparedPEERSjoint[l:], preparedPEERSjoint[l+1:])
											preparedPEERSjoint[len(preparedPEERSjoint)-1] = ""
											preparedPEERSjoint = preparedPEERSjoint[:len(preparedPEERSjoint)-1]
											break
										}
									}
								}

								// delete finished object from openNewBlockProposals: here always the first one in the slice
								copy(openNewApprovedJointBlockProposals[0:], openNewApprovedJointBlockProposals[1:])
								openNewApprovedJointBlockProposals[len(openNewApprovedJointBlockProposals)-1] = ""
								openNewApprovedJointBlockProposals = openNewApprovedJointBlockProposals[:len(openNewApprovedJointBlockProposals)-1]

								continue
							} //involved but not the main proposer

							continue
						} //not involved

					} //This is only executed if peer is not involved!

					if flag_involved == false {

						// check if timeout is already reached
						t_proposal := proposedBlock.Timestamp
						t_proposal_time, err := time.Parse(time.RFC850, t_proposal)
						if err != nil {
							log.Fatal(err)
						}
						t := time.Now()
						t_format := t.Format(time.RFC850)
						t_now_time, err := time.Parse(time.RFC850, t_format)
						if err != nil {
							log.Fatal(err)
						}
						//compare: time diff in seconds
						diff := t_now_time.Sub(t_proposal_time).Seconds()

						if  diff < votingTimeOut {

							// not involved peers are allowed to vote
							fmt.Printf("New joint block proposal from peer <%s> received and unpacked: \n", sender)
							fmt.Println("The following peers were involved: %s\n", involvedProposers_parsed)

							//mutex.Lock()
							proposedBlock_format, err := json.MarshalIndent(proposedBlock, "", "")
							if err != nil {
								log.Fatal(err)
							}
							fmt.Printf("\x1b[31m%s\x1b[0m> \n", string(proposedBlock_format))

							//save globally for corresponding vote
							currentBCProposal = newreceivedjointBlockchainProposal
							currentBlockProposal = proposedBlock

							fmt.Printf("Do you agree with the jointly proposed changes in block index %s?\n", proposedBlock.Index)
							fmt.Println("If yes: enter <j-yes>; if no: enter <j-no>:")

						// Timeout reached
						} else if  diff > votingTimeOut {

							// Write into variable, to be sent and read later
							newBlockchainProposal_bytes, err := json.Marshal(newreceivedjointBlockchainProposal)
							if err != nil {
								log.Println(err)
							}

							// write vote into variable and send
							var msg_3 strings.Builder
							senderID := ownPeerInfo["PeerID"].(string)
							senderID = senderID + string(";")
							switchcase := "myVoteOnNewApprovedJointBlockProposal;"
							msg_3.WriteString(senderID)
							msg_3.WriteString(switchcase)
							msg_3.WriteString(string(newBlockchainProposal_bytes) + string(";"))
							msg_3.WriteString("timeout")
							msg_3_send := msg_3.String()

							// broadcast with PubSub
							pubsub_msg := []byte(msg_3_send)
							go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

							// Send and wait for result
							fmt.Println("Timeout! Automatic vote sent! Waiting for result...")

							//Safe block for verification later
							verifyJointBlockProposals = append(verifyJointBlockProposals, proposedBlock)


							// delete finished object from queue: here always the first one in the slice
							copy(openNewApprovedJointBlockProposals[0:], openNewApprovedJointBlockProposals[1:])
							openNewApprovedJointBlockProposals[len(openNewApprovedJointBlockProposals)-1] = ""
							openNewApprovedJointBlockProposals = openNewApprovedJointBlockProposals[:len(openNewApprovedJointBlockProposals)-1]
						}
					} //not involved

				} //consensus reached

				// not enough prepared messages within timeframe --> delete proposal and notify others (Main proposer)
				if diff > proposalTimeOut && jointProposalEnoughPrepared == false {
					fmt.Println("No consensus reached! Delete proposal...")

					// delete finished object from openNewBlockProposals: here always the first one in the slice
					copy(openNewApprovedJointBlockProposals[0:], openNewApprovedJointBlockProposals[1:])
					openNewApprovedJointBlockProposals[len(openNewApprovedJointBlockProposals)-1] = ""
					openNewApprovedJointBlockProposals = openNewApprovedJointBlockProposals[:len(openNewApprovedJointBlockProposals)-1]

					//Delete prepared_messages_single from lists (if inside)
					preparedSentjoint = false
					jointProposalEnoughPrepared = false //new

					if len(preparedHASHjoint) > 0 { //check if something is in this list, if not ignore
						for l := 0; l < len(preparedHASHjoint); l++ {
							if preparedHASHjoint[l] == proposedBlock.Hash {
								copy(preparedHASHjoint[l:], preparedHASHjoint[l+1:])
								preparedHASHjoint[len(preparedHASHjoint)-1] = ""
								preparedHASHjoint = preparedHASHjoint[:len(preparedHASHjoint)-1]
								copy(preparedPEERSjoint[l:], preparedPEERSjoint[l+1:])
								preparedPEERSjoint[len(preparedPEERSjoint)-1] = ""
								preparedPEERSjoint = preparedPEERSjoint[:len(preparedPEERSjoint)-1]
								break
							}
						}
					}

					//for message, to be compared later
					proposedBlock_format, err := json.MarshalIndent(proposedBlock, "", "")
					if err != nil {
						log.Fatal(err)
					}

					//extract main proposer
					proposers := strings.Split(proposedBlock.Proposer, ",")
					mainProposer := proposers[0]

					// send message to main proposer update metrics and delete from list --> maybe without message!
					var msg_3 strings.Builder
					senderID := ownPeerInfo["PeerID"].(string)
					senderID = senderID + string(";")
					switchcase := "PREPAREDFAILJOINT;"
					msg_3.WriteString(senderID)
					msg_3.WriteString(switchcase)
					msg_3.WriteString(string(proposedBlock.Hash) + string(";"))
					msg_3.WriteString(string(mainProposer + string(";")))
					msg_3.WriteString(string(proposedBlock_format))
					msg_3_send := msg_3.String()

					// broadcast with PubSub:
					pubsub_msg := []byte(msg_3_send)
					go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

					continue
				} //no consensus reached

			} //else if switchcase == "myVoteOnNewBlockProposal" {
		} //end queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		//joint proposal voting results
		if len(openVotesOnNewApprovedJointBlockProposals) > 0 {
			// read from queue:
			currentContent := openVotesOnNewApprovedJointBlockProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			if switchcase == "myVoteOnNewApprovedJointBlockProposal" {

				//read incoming chain
				receivedAcceptedBlockchain := receivedContent_parsed[2]

				//extract vote
				peerVoteJoint := receivedContent_parsed[3]
				//sender := receivedContent_parsed[0]

				// create new blockchain that contains the new string
				newAcceptedBlockchain := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedAcceptedBlockchain), &newAcceptedBlockchain); err != nil {
					log.Fatal(err)
				}
				// extract the latest (=new unvalidated) block
				proposedBlock := newAcceptedBlockchain[len(newAcceptedBlockchain)-1]

				// more than one proposer: extract them
				involvedProposers_parsed := strings.Split(proposedBlock.Proposer, ",")
				//numbInvolvedJointPeers := len(involvedProposers_parsed)

				// modify to string in order to compare it with existing ones
				proposedBlock_format, err := json.MarshalIndent(proposedBlock, "", "")
				if err != nil {
					log.Fatal(err)
				}

				//main proposer does this
				if involvedProposers_parsed[0] == pid_own {

					// peer received a vote for an already finsihed proposal
					ownProposal_notInList2 := true
					timeout := false

					// Check if vote belongs to own proposal; if yes: save vote
					for i := 0; i < len(myOpenApprovedJointBlockProposals); i++ {
						if strings.Compare(myOpenApprovedJointBlockProposals[i], string(proposedBlock_format)) == 0 {
							ownProposal_notInList2 = false
							fmt.Printf("This vote corresponds to one of my open approved joint proposals!Save and process votes...\n")
							// save peerVote to corresponding proposal
							if strings.HasPrefix(peerVoteJoint, "agree") {
								posVotesJoint[i] = posVotesJoint[i] + 1
							} else if strings.HasPrefix(peerVoteJoint, "dis") {
								negVotesJoint[i] = negVotesJoint[i] + 1
							} else if strings.HasPrefix(peerVoteJoint, "time") {
								timeout = true
							}

							// after check; delete finished object from openVotesOnNewApprovedJointBlockProposals
							copy(openVotesOnNewApprovedJointBlockProposals[0:], openVotesOnNewApprovedJointBlockProposals[1:])
							openVotesOnNewApprovedJointBlockProposals[len(openVotesOnNewApprovedJointBlockProposals)-1] = ""
							openVotesOnNewApprovedJointBlockProposals = openVotesOnNewApprovedJointBlockProposals[:len(openVotesOnNewApprovedJointBlockProposals)-1]

							//Voting
							requValidatorsJoint_float := float64(len(GlobalPeerList) - len(involvedProposers_parsed)) // all nodes -1 (proposer) have to vote before result is checked!
							requiredThreshold_abs_float := math.Ceil(2. / 3 * requValidatorsJoint_float)              //2/3 of the required voters for majority
							var requValidatorsJoint int = int(requValidatorsJoint_float)
							var requiredThreshold_abs int = int(requiredThreshold_abs_float)

							j := i

							//Check if enough peers have voted
							if (posVotesJoint[j]+negVotesJoint[j] < requValidatorsJoint)  && timeout == false {
								fmt.Println("Not yet enough votes! Wait...")
								continue
							}

							if (posVotesJoint[j]+negVotesJoint[j] < requValidatorsJoint)  && timeout == true {
								fmt.Println("Timeout! Check if majority was reached anyways...")

							}

							//if enough peers have voted, check who won
							if posVotesJoint[j] >= requiredThreshold_abs {
								fmt.Println("Proposal has enough votes and reached a majority: Accepted \n")

								// Reward for main proposer is double deposit/stake: 3x to get back stake and then double it
								proposalReward := float64(3 * myRequStakeEachPeer[j])
								TokenBalanceStake := float64(ownPeerInfo["TokenBalance"].(float64))
								UpdateTokenBalance := TokenBalanceStake + (proposalReward+1) //+1 as involved peer also get one token for validation, then equal!
								ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalance)

								numberOfApprovedProposals := float64(ownPeerInfo["ApprovedProposals"].(float64))
								NewNumberOfApprovedProposals := numberOfApprovedProposals + float64(1)
								ownPeerInfo["ApprovedProposals"] = interface{}(NewNumberOfApprovedProposals)

								AuthorMetrics_parsed, err := json.Marshal(ownPeerInfo)
								if err != nil {
									panic(err)
								}

								// update ProposalMETRICS:
								requStake_all := float64(float64(len(involvedProposers_parsed)) * float64(myRequStakeEachPeer[j]))
								t0_create := startingTimeJointProp[j]
								t_diff := time.Since(t0_create)
								t_diff_string := fmt.Sprintf("%v", t_diff)
								participation_abs := float64(posVotesJoint[j] + negVotesJoint[j])
								newProposalMetrics := &ProposalMetrics{requStake_all, t_diff_string, true, float64(posVotesJoint[j]), participation_abs}
								ProposalMetrics_parsed, err := json.Marshal(newProposalMetrics)
								if err != nil {
									panic(err)
								}

								// update NetworkMETRICS: total network proposals
								networkMetrics := &NetworkMetrics{len(GlobalPeerList)}
								networkMetrics_parsed, err := json.Marshal(networkMetrics)
								if err != nil {
									panic(err)
								}

								// Make new proposal block with new-final data:
								newAcceptedBlock, err := generateBlock(Blockchain[len(Blockchain)-1], proposedBlock.File, proposedBlock.Proposer, string(AuthorMetrics_parsed), string(ProposalMetrics_parsed), string(networkMetrics_parsed))
								if err != nil {
									log.Println(err)
									continue
								}

								// Check if generated block is valid (not in terms of consensus, but Hashing, Index etc.!)
								if isBlockValid(newAcceptedBlock, Blockchain[len(Blockchain)-1]) {
									mutex.Lock()
									//Append new proposal to chain - just for transfer - decrypt later
									newAcceptedBlockchain = append(Blockchain, newAcceptedBlock)
									mutex.Unlock()
								}

								fmt.Println("New accepted block was successfully re-created!")

								// Write into own Terminal
								mutex.Lock()
								newAcceptedBlock_format, err := json.MarshalIndent(newAcceptedBlock, "", "")
								if err != nil {
									log.Fatal(err)
								}
								fmt.Printf("\x1b[33m%s\x1b[0m> \n", string(newAcceptedBlock_format))
								mutex.Unlock()

								// make bytes for msg
								newAcceptedBlockchain_bytes, err := json.Marshal(newAcceptedBlockchain)
								if err != nil {
									log.Println(err)
								}

								// append requStakeEachPeer to message as a string
								requStakeEachPeer_string := fmt.Sprintf("%f", requStakeEachPeer)

								// Write into variable, to be sent and read later
								var msg_8 strings.Builder
								senderID := ownPeerInfo["PeerID"].(string)
								senderID = senderID + string(";")
								switchcase := "FinalBlockJoint;"
								msg_8.WriteString(senderID)
								msg_8.WriteString(switchcase)
								msg_8.WriteString(string(newAcceptedBlockchain_bytes) + string(";"))
								msg_8.WriteString(requStakeEachPeer_string)
								msg_8_send := msg_8.String()

								// broadcast with PubSub
								pubsub_msg := []byte(msg_8_send)
								go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

								// Send and wait for others to append
								fmt.Println("Sent to other peers!")

								// sender can append here directly
								// Check if new received accpeted chain is longer than older one, update global Blockchain
								mutex.Lock()
								if len(newAcceptedBlockchain) > len(Blockchain) {
									Blockchain = newAcceptedBlockchain
									Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
									if err != nil {
										log.Fatal(err)
									}

									fmt.Println("The latest valid Blockchain is: ")
									fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))

								}
								mutex.Unlock()

								// delete finished object from myOpenBlockProposals
								copy(myOpenApprovedJointBlockProposals[j:], myOpenApprovedJointBlockProposals[j+1:])
								myOpenApprovedJointBlockProposals[len(myOpenApprovedJointBlockProposals)-1] = ""
								myOpenApprovedJointBlockProposals = myOpenApprovedJointBlockProposals[:len(myOpenApprovedJointBlockProposals)-1]

								// also delete corresponding votes to this proposal!
								copy(posVotesJoint[j:], posVotesJoint[j+1:])
								posVotesJoint[len(posVotesJoint)-1] = 0
								posVotesJoint = posVotesJoint[:len(posVotesJoint)-1]
								copy(negVotesJoint[j:], negVotesJoint[j+1:])
								negVotesJoint[len(negVotesJoint)-1] = 0
								negVotesJoint = negVotesJoint[:len(negVotesJoint)-1]

								//delete the requStakes entry
								copy(myRequStakeEachPeer[j:], myRequStakeEachPeer[j+1:])
								myRequStakeEachPeer[len(myRequStakeEachPeer)-1] = 0
								myRequStakeEachPeer = myRequStakeEachPeer[:len(myRequStakeEachPeer)-1]

								// delete corresponding time entry for calculation
								copy(startingTimeJointProp[j:], startingTimeJointProp[j+1:])
								startingTimeJointProp[len(startingTimeJointProp)-1] = time.Now()
								startingTimeJointProp = startingTimeJointProp[:len(startingTimeJointProp)-1]

								continue

							}

							if negVotesJoint[j] >= requiredThreshold_abs || ((posVotesJoint[j]+negVotesJoint[j] >= requValidatorsJoint) && negVotesJoint[j] < requiredThreshold_abs) || (timeout == true && (negVotesJoint[j] < requiredThreshold_abs)) {
								fmt.Printf("Proposal has enough votes and reached a majority: Declined \n")

								// Reward is double deposit/stake: 3x to get back stake and then double it
								numberOfDeclinedProposals := float64(ownPeerInfo["DeclinedProposals"].(float64))
								NewNumberOfDeclinedProposals := numberOfDeclinedProposals + float64(1)
								ownPeerInfo["DeclinedProposals"] = interface{}(NewNumberOfDeclinedProposals)

								// Write into variable, to be sent and read later
								var msg_8 strings.Builder
								senderID := ownPeerInfo["PeerID"].(string)
								senderID = senderID + string(";")
								switchcase := "DeclinedProposalJoint;"
								msg_8.WriteString(senderID)
								msg_8.WriteString(switchcase)
								msg_8.WriteString(proposedBlock.Proposer + string(";")) //necessary that they can update their metrics
								msg_8.WriteString(proposedBlock.File)
								msg_8_send := msg_8.String()

								// broadcast with PubSub
								pubsub_msg := []byte(msg_8_send)
								go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

								// delete finished object from myOpenBlockProposals
								copy(myOpenApprovedJointBlockProposals[j:], myOpenApprovedJointBlockProposals[j+1:])
								myOpenApprovedJointBlockProposals[len(myOpenApprovedJointBlockProposals)-1] = ""
								myOpenApprovedJointBlockProposals = myOpenApprovedJointBlockProposals[:len(myOpenApprovedJointBlockProposals)-1]

								// also delete corresponding votes to this proposal!
								copy(posVotesJoint[j:], posVotesJoint[j+1:])
								posVotesJoint[len(posVotesJoint)-1] = 0
								posVotesJoint = posVotesJoint[:len(posVotesJoint)-1]
								copy(negVotesJoint[j:], negVotesJoint[j+1:])
								negVotesJoint[len(negVotesJoint)-1] = 0
								negVotesJoint = negVotesJoint[:len(negVotesJoint)-1]

								//delete the requStakes entry
								copy(myRequStakeEachPeer[j:], myRequStakeEachPeer[j+1:])
								myRequStakeEachPeer[len(myRequStakeEachPeer)-1] = 0
								myRequStakeEachPeer = myRequStakeEachPeer[:len(myRequStakeEachPeer)-1]

								// delete corresponding time entry for calculation
								copy(startingTimeJointProp[j:], startingTimeJointProp[j+1:])
								startingTimeJointProp[len(startingTimeJointProp)-1] = time.Now()
								startingTimeJointProp = startingTimeJointProp[:len(startingTimeJointProp)-1]

								// show latest valid blockchain
								Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
								if err != nil {
									log.Fatal(err)
								}

								fmt.Println("The latest valid Blockchain is: ")
								fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))

								continue
							} //declined
						} //proposal i
					} // for all my Proposals

					// peer received a vote for an already finsihed proposal
					if ownProposal_notInList2 == true {
						// after check; delete finished object from openVotesOnNewBlockProposals
						fmt.Println("Vote cannot be assigned to an open proposal! Delete...")
						copy(openVotesOnNewApprovedJointBlockProposals[0:], openVotesOnNewApprovedJointBlockProposals[1:])
						openVotesOnNewApprovedJointBlockProposals[len(openVotesOnNewApprovedJointBlockProposals)-1] = ""
						openVotesOnNewApprovedJointBlockProposals = openVotesOnNewApprovedJointBlockProposals[:len(openVotesOnNewApprovedJointBlockProposals)-1]
						continue
					}

				} else { //author is own peer ID = creator

					// after check; delete finished object from openVotesOnNewApprovedJointBlockProposals: to not block the lists!
					copy(openVotesOnNewApprovedJointBlockProposals[0:], openVotesOnNewApprovedJointBlockProposals[1:])
					openVotesOnNewApprovedJointBlockProposals[len(openVotesOnNewApprovedJointBlockProposals)-1] = ""
					openVotesOnNewApprovedJointBlockProposals = openVotesOnNewApprovedJointBlockProposals[:len(openVotesOnNewApprovedJointBlockProposals)-1]

				} //author
			} //switchcase

		} //end queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		//append final joint block
		if len(FinalBlockNewApprovedJointBlockProposals) > 0 {
			// read from queue:
			currentContent := FinalBlockNewApprovedJointBlockProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			if switchcase == "FinalBlockJoint" {

				fmt.Println("Joint proposal was accepted! Verify and append final block...")

				sender := receivedContent_parsed[0]
				receivedAcceptedBlockchain := receivedContent_parsed[2]
				requStakeEachPeer_string := receivedContent_parsed[3]
				requStakeEachPeer_string = strings.Replace(requStakeEachPeer_string, "\n", "", -1)
				requStakeEachPeer, _ = strconv.ParseFloat(requStakeEachPeer_string, 64)

				// create new blockchain that contains the new string
				newAcceptedBlockchain := make([]Block, 0)
				if err := json.Unmarshal([]byte(receivedAcceptedBlockchain), &newAcceptedBlockchain); err != nil {
					log.Fatal(err)
				}

				// extract the latest block to parse Author/Proposer
				proposedBlock := newAcceptedBlockchain[len(newAcceptedBlockchain)-1]

				// more than one proposer: extract them
				involvedProposers_parsed := strings.Split(proposedBlock.Proposer, ",")
				numbInvolvedJointPeers := len(involvedProposers_parsed)

				//Check who is the peer: sender, involved, not involved
				for z := 0; z < numbInvolvedJointPeers; z++ {
					if involvedProposers_parsed[z] == pid_own {
						// involved but not main proposer=sender
						if sender != pid_own {
							// update metrics for successful joint proposal
							// Reward is double deposit/stake: 3x to get back stake and then double it
							proposalReward := float64(3 * requStakeEachPeer)
							TokenBalanceStake := float64(ownPeerInfo["TokenBalance"].(float64))
							UpdateTokenBalance := TokenBalanceStake + proposalReward
							ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalance)

							numberOfApprovedProposals := float64(ownPeerInfo["ApprovedProposals"].(float64))
							NewNumberOfApprovedProposals := numberOfApprovedProposals + float64(1)
							ownPeerInfo["ApprovedProposals"] = interface{}(NewNumberOfApprovedProposals)

							// Check if new received accpeted chain is longer than older one, update global Blockchain
							mutex.Lock()
							if len(newAcceptedBlockchain) > len(Blockchain) {
								Blockchain = newAcceptedBlockchain
								Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
								if err != nil {
									log.Fatal(err)
								}

								fmt.Println("The latest valid Blockchain is: ")
								fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))

							}
							mutex.Unlock()
						}
					}
				}

				//Not the sender
				if sender != pid_own {

					// Check if is valid: compare if it is in list and hash/link has not changed
					// TODO: make more secure by also checking if it had enough votes.....
					proposer_received := proposedBlock.Proposer
					link_received := proposedBlock.File
					for j := 0; j < len(verifyJointBlockProposals); j++ {
						if verifyJointBlockProposals[j].File == link_received && verifyJointBlockProposals[j].Proposer == proposer_received {
							fmt.Println("New Block verified! Appending...")

							// Check if new received accpeted chain is longer than older one, update global Blockchain
							mutex.Lock()
							if len(newAcceptedBlockchain) > len(Blockchain) {
								Blockchain = newAcceptedBlockchain
								Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
								if err != nil {
									log.Fatal(err)
								}

								fmt.Println("The latest valid Blockchain is: ")
								fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))

							}
							mutex.Unlock()
						}

						//Delete from list
						copy(verifyJointBlockProposals[j:], verifyJointBlockProposals[j+1:])
						verifyJointBlockProposals[len(verifyJointBlockProposals)-1] = proposedBlock //write any block, is deleted afterwards
						verifyJointBlockProposals = verifyJointBlockProposals[:len(verifyJointBlockProposals)-1]
						break
					}

				} //not the proposer

				// after check; delete finished object from FinalBlockNewApprovedJointBlockProposals
				copy(FinalBlockNewApprovedJointBlockProposals[0:], FinalBlockNewApprovedJointBlockProposals[1:])
				FinalBlockNewApprovedJointBlockProposals[len(FinalBlockNewApprovedJointBlockProposals)-1] = ""
				FinalBlockNewApprovedJointBlockProposals = FinalBlockNewApprovedJointBlockProposals[:len(FinalBlockNewApprovedJointBlockProposals)-1]

				continue

			} //end finalBlock
		} //queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// declined block received: update metrics
		if len(DeclinedBlockNewApprovedJointBlockProposals) > 0 {
			// read from queue:
			currentContent := DeclinedBlockNewApprovedJointBlockProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]

			if switchcase == "DeclinedProposalJoint" {

				fmt.Println("Proposal was declined! Update metrics...")

				sender := receivedContent_parsed[0]
				link_received := receivedContent_parsed[3]
				involvedProposers_parsed_strg := receivedContent_parsed[2]
				involvedProposers_parsed := strings.Split(involvedProposers_parsed_strg, ",")
				numbInvolvedJointPeers := len(involvedProposers_parsed)

				//make slice []string from "string"
				var involvedProposers []string
				for z := 0; z < len(involvedProposers_parsed); z++ {
					involvedProposers = append(involvedProposers, involvedProposers_parsed[z])
				}

				//Check who is the peer: sender, involved, not involved
				for z := 0; z < numbInvolvedJointPeers; z++ {
					if involvedProposers_parsed[z] == pid_own {
						// involved but not main proposer=sender
						if sender != pid_own {
							//update metrics for unsuccessful joint proposal
							numberOfDeclinedProposals := float64(ownPeerInfo["DeclinedProposals"].(float64))
							NewNumberOfDeclinedProposals := numberOfDeclinedProposals + float64(1)
							ownPeerInfo["DeclinedProposals"] = interface{}(NewNumberOfDeclinedProposals)
						}
					}
				}

				if sender != pid_own {

					//delete from list
					for j := 0; j < len(verifyJointBlockProposals); j++ {
						if verifyJointBlockProposals[j].File == link_received {
							fmt.Println("Delete corresponding proposal from verification list...")

							//Delete from list
							randomBlock := verifyJointBlockProposals[j]
							copy(verifyJointBlockProposals[j:], verifyJointBlockProposals[j+1:])
							verifyJointBlockProposals[len(verifyJointBlockProposals)-1] = randomBlock //write any block, will be deleted later on
							verifyJointBlockProposals = verifyJointBlockProposals[:len(verifyJointBlockProposals)-1]
							break
						}
					}

					// show latest valid blockchain
					Blockchain_bytes, err := json.MarshalIndent(Blockchain, "", "")
					if err != nil {
						log.Fatal(err)
					}

					fmt.Println("The latest valid Blockchain is: ")
					fmt.Printf("\x1b[32m%s\x1b[0m> \n", string(Blockchain_bytes))
				} //sender != peerIDown

				// after check; delete finished object from DeclinedBlockNewApprovedJointBlockProposals
				copy(DeclinedBlockNewApprovedJointBlockProposals[0:], DeclinedBlockNewApprovedJointBlockProposals[1:])
				DeclinedBlockNewApprovedJointBlockProposals[len(DeclinedBlockNewApprovedJointBlockProposals)-1] = ""
				DeclinedBlockNewApprovedJointBlockProposals = DeclinedBlockNewApprovedJointBlockProposals[:len(DeclinedBlockNewApprovedJointBlockProposals)-1]

				continue

			} // end DeclinedProposal
		} //queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		//---peers----

		// other peer wants to remove oneself
		if len(openRemoveOwnPeerAccountProposals) > 0 {
			// read from queue:
			currentContent := openRemoveOwnPeerAccountProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]
			sender := receivedContent_parsed[0]

			if switchcase == "removeOwnPeerAccount" {

				if sender != pid_own {
					fmt.Printf("\x1b[33m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Printf("New peer removal:\n")
					fmt.Printf("Peer <%s> will leave the network by his/her own decision.\n", sender)
					fmt.Printf("\x1b[33m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

					//remove from GlobalPeerList and network metrics!
					for k := 0; k < len(GlobalPeerList); k++ {
						if sender == GlobalPeerList[k] {
							copy(GlobalPeerList[k:], GlobalPeerList[k+1:])
							GlobalPeerList[len(GlobalPeerList)-1] = ""
							GlobalPeerList = GlobalPeerList[:len(GlobalPeerList)-1]
							continue
						}
					}
				}
			} //peer own removal

			copy(openRemoveOwnPeerAccountProposals[0:], openRemoveOwnPeerAccountProposals[1:])
			openRemoveOwnPeerAccountProposals[len(openRemoveOwnPeerAccountProposals)-1] = ""
			openRemoveOwnPeerAccountProposals = openRemoveOwnPeerAccountProposals[:len(openRemoveOwnPeerAccountProposals)-1]
			continue

		} //queue remove oneself

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// add new peer
		if len(openAddPeerAccountProposals) > 0 {
			// read from queue:
			currentContent := openAddPeerAccountProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			switchcase := receivedContent_parsed[1]
			sender := receivedContent_parsed[0]
			proposer := receivedContent_parsed[4]
			peer2Add := receivedContent_parsed[2]
			reason := receivedContent_parsed[3]

			if switchcase == "addNewPeerProposal" {

				if sender != pid_own {

					//save globally for corresponding vote
					currentPeerID2AddProposal = peer2Add
					currentPeerID2AddProposer = proposer

					//For Voting
					fmt.Printf("\x1b[31m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Printf("New proposal to add a new peer to the network:\n")
					fmt.Printf("Peer <%s> proposed to add a new peer with ID <%s> to the network.\n", proposer, peer2Add)
					fmt.Printf("The reason is: %s\n", reason)
					fmt.Printf("If you agree to add this peer, enter <add>, if not enter <not-add>:\n")
					fmt.Printf("\x1b[31m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
				}
			}
		} //end queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// remove other peer
		if len(openRemovePeerAccountProposals) > 0 {
			// read from queue:
			currentContent := openRemovePeerAccountProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]
			sender := receivedContent_parsed[0]
			proposer := receivedContent_parsed[4]
			peer2Remove := receivedContent_parsed[2]
			reason := receivedContent_parsed[3]

			if switchcase == "removeExistingPeerProposal" {

				//save globally for corresponding vote
				currentPeerID2RemoveProposal = peer2Remove
				currentPeerID2RemoveProposer = proposer

				if pid_own == peer2Remove {
					//For Voting
					fmt.Printf("\x1b[31m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Printf("New proposal to remove an existing peer from the network:\n")
					fmt.Printf("Peer <%s> proposed to remove you from the network.\n", sender)
					fmt.Printf("The reason is: %s\n", reason)
					fmt.Printf("If you agree to remove yourself, enter <remove>, if not enter <not-remove>:\n")
					fmt.Printf("\x1b[31m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

				} else if pid_own != peer2Remove {

					//msg := "New proposal to remove a peer from the network:"
					//fmt.Printf("\x1b[31m%s\x1b[0m \n", string(msg))
					fmt.Printf("\x1b[31m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Printf("New proposal to remove an existing peer from the network:\n")
					fmt.Printf("Peer <%s> proposed to remove the peer wiht ID <%s> from the network.\n", proposer, peer2Remove)
					fmt.Printf("The reason is: %s\n", reason)
					fmt.Printf("If you agree to remove this peer, enter <remove>, if not enter <not-remove>:\n")
					fmt.Printf("\x1b[31m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
				}

			}
		} //queue remove existing peer

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		//add new peer votes
		if len(openVotesAddPeerAccountProposals) > 0 {
			// read from queue:
			currentContent := openVotesAddPeerAccountProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]
			//sender := receivedContent_parsed[0]
			peer2Add := receivedContent_parsed[2]
			proposer := receivedContent_parsed[3]
			peerVote := receivedContent_parsed[4]

			if switchcase == "myVoteOnAddPeerProposal" {
				//vote corresponds to one of mine proposals
				if proposer == pid_own {

					ownProposal_notInList6 := true

					// Check if vote belongs to own proposal; if yes: save vote
					for i := 0; i < len(myOpenPeerProposals); i++ {
						if strings.Compare(myOpenPeerProposals[i], string(peer2Add)) == 0 {

							ownProposal_notInList6 = false
							fmt.Printf("This vote corresponds to one of my open peer proposals! Save and process votes...\n")
							// save peerVote to corresponding proposal
							if strings.HasPrefix(peerVote, "agree") {
								posPeerVotes[i] = posPeerVotes[i] + 1
							} else if strings.HasPrefix(peerVote, "dis") {
								negPeerVotes[i] = negPeerVotes[i] + 1
							}

							// after check; delete finished object from openVotesAddPeerAccountProposals
							copy(openVotesAddPeerAccountProposals[0:], openVotesAddPeerAccountProposals[1:])
							openVotesAddPeerAccountProposals[len(openVotesAddPeerAccountProposals)-1] = ""
							openVotesAddPeerAccountProposals = openVotesAddPeerAccountProposals[:len(openVotesAddPeerAccountProposals)-1]

							//Check if for one of the own proposals a majority of votes is already reached:
							//Voting
							requValidators_float := float64(len(GlobalPeerList) - 1)                // all nodes -1 (proposer) have to vote before result is checked!
							requiredThreshold_abs_float := math.Ceil(2. / 3 * requValidators_float) //2/3 of the required voters for majority
							var requValidators int = int(requValidators_float)
							var requiredThreshold_abs int = int(requiredThreshold_abs_float)

							//for j := 0; j < len(myOpenBlockProposals); j++ {
							j := i

							//Check if enough peers have voted
							//if posPeerVotes[j]+negPeerVotes[j] < requValidators {
							//	fmt.Println("Not yet enough votes! Wait...")
							//	continue
							//}

							//if enough peers have voted, check who won
							if posPeerVotes[j] >= requiredThreshold_abs {
								fmt.Println("Proposal has enough votes and reached a majority: Accepted \n")

								fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
								fmt.Printf("Majority reached! Peer can be added to the network! Updating metrics...\n")
								fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

								//add to list
								confirmedPeers2Add = append(confirmedPeers2Add, peer2Add)

								// Reward is double deposit/stake: 3x to get back stake and then double it
								proposalReward := float64(3 * requStakeAddRemove)
								TokenBalanceStake := float64(ownPeerInfo["TokenBalance"].(float64))
								UpdateTokenBalance := TokenBalanceStake + proposalReward
								ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalance)

								numberOfApprovedProposals := float64(ownPeerInfo["ApprovedProposals"].(float64))
								NewNumberOfApprovedProposals := numberOfApprovedProposals + float64(1)
								ownPeerInfo["ApprovedProposals"] = interface{}(NewNumberOfApprovedProposals)

								// broadcast with rest of peers
								var msg_8 strings.Builder
								senderID := ownPeerInfo["PeerID"].(string)
								senderID = senderID + string(";")
								switchcase := "FinalAddPeer;"
								msg_8.WriteString(senderID)
								msg_8.WriteString(switchcase)
								msg_8.WriteString(string(peer2Add) + string(";"))
								msg_8.WriteString(proposer + string(";"))
								msg_8.WriteString(strconv.Itoa(posPeerVotes[j]))
								msg_8_send := msg_8.String()

								// broadcast with PubSub
								pubsub_msg := []byte(msg_8_send)
								go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

								// Send and wait for others to append
								fmt.Println("Sent to other peers!")

								// delete finished object from myOpenBlockProposals
								copy(myOpenPeerProposals[j:], myOpenPeerProposals[j+1:])
								myOpenPeerProposals[len(myOpenPeerProposals)-1] = ""
								myOpenPeerProposals = myOpenPeerProposals[:len(myOpenPeerProposals)-1]

								// also delete corresponding votes to this proposal!
								copy(posPeerVotes[j:], posPeerVotes[j+1:])
								posPeerVotes[len(posPeerVotes)-1] = 0
								posPeerVotes = posPeerVotes[:len(posPeerVotes)-1]
								copy(negPeerVotes[j:], negPeerVotes[j+1:])
								negPeerVotes[len(negPeerVotes)-1] = 0
								negPeerVotes = negPeerVotes[:len(negPeerVotes)-1]

								continue

							}

							if negPeerVotes[j] >= requiredThreshold_abs || ((posPeerVotes[j]+negPeerVotes[j] >= requValidators) && negPeerVotes[j] < requiredThreshold_abs) {
								fmt.Printf("Proposal has enough votes and reached a majority: Declined \n")

								fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
								fmt.Printf("No majority reached! Peer will not be added to the network! Updating metrics...\n")
								fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

								// Reward is double deposit/stake: 3x to get back stake and then double it
								numberOfDeclinedProposals := float64(ownPeerInfo["DeclinedProposals"].(float64))
								NewNumberOfDeclinedProposals := numberOfDeclinedProposals + float64(1)
								ownPeerInfo["DeclinedProposals"] = interface{}(NewNumberOfDeclinedProposals)

								// Write into variable, to be sent and read later
								var msg_8 strings.Builder
								senderID := ownPeerInfo["PeerID"].(string)
								senderID = senderID + string(";")
								switchcase := "FinalAddPeerDeclined;"
								msg_8.WriteString(senderID)
								msg_8.WriteString(switchcase)
								msg_8.WriteString(string(proposer))
								msg_8_send := msg_8.String()

								// broadcast with PubSub
								pubsub_msg := []byte(msg_8_send)
								go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

								// delete finished object from myOpenBlockProposals
								copy(myOpenPeerProposals[j:], myOpenPeerProposals[j+1:])
								myOpenPeerProposals[len(myOpenPeerProposals)-1] = ""
								myOpenPeerProposals = myOpenPeerProposals[:len(myOpenPeerProposals)-1]

								// also delete corresponding votes to this proposal!
								copy(posPeerVotes[j:], posPeerVotes[j+1:])
								posPeerVotes[len(posPeerVotes)-1] = 0
								posPeerVotes = posPeerVotes[:len(posPeerVotes)-1]
								copy(negPeerVotes[j:], negPeerVotes[j+1:])
								negPeerVotes[len(negPeerVotes)-1] = 0
								negPeerVotes = negPeerVotes[:len(negPeerVotes)-1]

								continue

							} //Declined

						} //belongs to proposal i
					} // for loop own proposals

					// peer received a vote for an already finsihed proposal
					if ownProposal_notInList6 == true {
						// after check; delete finished object from openVotesOnNewBlockProposals
						fmt.Println("Vote cannot be assigned to an open proposal! Delete...")
						copy(openVotesAddPeerAccountProposals[0:], openVotesAddPeerAccountProposals[1:])
						openVotesAddPeerAccountProposals[len(openVotesAddPeerAccountProposals)-1] = ""
						openVotesAddPeerAccountProposals = openVotesAddPeerAccountProposals[:len(openVotesAddPeerAccountProposals)-1]

						continue
					}

				} else { //author is not own peer ID = not creator

					// delete finished object from openVotesOnNewBlockProposals
					copy(openVotesAddPeerAccountProposals[0:], openVotesAddPeerAccountProposals[1:])
					openVotesAddPeerAccountProposals[len(openVotesAddPeerAccountProposals)-1] = ""
					openVotesAddPeerAccountProposals = openVotesAddPeerAccountProposals[:len(openVotesAddPeerAccountProposals)-1]
				}
			}
		} //queue votes add new peer

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// add other peer accepted
		if len(openFinalAddPeerAccountProposals) > 0 {
			// read from queue:
			currentContent := openFinalAddPeerAccountProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]
			peer2Add := receivedContent_parsed[2]
			majority := receivedContent_parsed[4]
			majority_int, _ := strconv.Atoi(majority)

			//proposer := receivedContent_parsed[3]

			if switchcase == "FinalAddPeer" {

				if pid_own != sender {

					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Printf("Proposal accepted: The network decided to add a peer:\n")
					fmt.Printf("Peer <%s> can now be added to the network! %v of %v peers in the network agreed!\n", peer2Add, majority_int+1, len(GlobalPeerList))
					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

					//add to list
					confirmedPeers2Add = append(confirmedPeers2Add, peer2Add)

					// delete finished object from openVotesOnNewBlockProposals
					copy(openFinalAddPeerAccountProposals[0:], openFinalAddPeerAccountProposals[1:])
					openFinalAddPeerAccountProposals[len(openFinalAddPeerAccountProposals)-1] = ""
					openFinalAddPeerAccountProposals = openFinalAddPeerAccountProposals[:len(openFinalAddPeerAccountProposals)-1]

					continue
				}
			}
		} //qeueue add final

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// add other peer accepted
		if len(openFinalAddPeerAccountProposalsDeclined) > 0 {
			// read from queue:
			currentContent := openFinalAddPeerAccountProposalsDeclined[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]
			peer2Add := receivedContent_parsed[2]
			//proposer := receivedContent_parsed[3]

			if switchcase == "FinalAddPeerDeclined" {

				if pid_own != sender {

					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Printf("Proposal declined! The network decided to not add a peer!\n")
					fmt.Printf("Peer <%s> will not be be added the network!\n", peer2Add)
					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

					// delete finished object from openVotesOnNewBlockProposals
					copy(openFinalAddPeerAccountProposalsDeclined[0:], openFinalAddPeerAccountProposalsDeclined[1:])
					openFinalAddPeerAccountProposalsDeclined[len(openFinalAddPeerAccountProposalsDeclined)-1] = ""
					openFinalAddPeerAccountProposalsDeclined = openFinalAddPeerAccountProposalsDeclined[:len(openFinalAddPeerAccountProposalsDeclined)-1]

					continue
				}
			}
		} //queue add final

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// remove other peer
		if len(openVotesRemovePeerAccountProposals) > 0 {
			// read from queue:
			currentContent := openVotesRemovePeerAccountProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]
			//sender := receivedContent_parsed[0]
			peer2Remove := receivedContent_parsed[2]
			proposer := receivedContent_parsed[3]
			peerVote := receivedContent_parsed[4]

			if switchcase == "myVoteOnRemovePeerProposal" {
				//vote corresponds to one of mine proposals
				if proposer == pid_own {

					ownProposal_notInList5 := true

					// Check if vote belongs to own proposal; if yes: save vote
					for i := 0; i < len(myOpenPeerProposals); i++ {
						if strings.Compare(myOpenPeerProposals[i], string(peer2Remove)) == 0 {

							ownProposal_notInList5 = false
							fmt.Printf("This vote corresponds to one of my open peer proposals! Save and process votes...\n")
							// save peerVote to corresponding proposal
							if strings.HasPrefix(peerVote, "agree") {
								posPeerVotes[i] = posPeerVotes[i] + 1
							} else if strings.HasPrefix(peerVote, "dis") {
								negPeerVotes[i] = negPeerVotes[i] + 1
							}

							// after check; delete finished object from openVotesRemovePeerAccountProposals
							copy(openVotesRemovePeerAccountProposals[0:], openVotesRemovePeerAccountProposals[1:])
							openVotesRemovePeerAccountProposals[len(openVotesRemovePeerAccountProposals)-1] = ""
							openVotesRemovePeerAccountProposals = openVotesRemovePeerAccountProposals[:len(openVotesRemovePeerAccountProposals)-1]

							//Check if for one of the own proposals a majority of votes is already reached:
							requValidators_float := float64(len(GlobalPeerList) - 1)                // all nodes -1 (proposer) have to vote before result is checked!
							requiredThreshold_abs_float := math.Ceil(2. / 3 * requValidators_float) //2/3 of the required voters for majority
							var requValidators int = int(requValidators_float)
							var requiredThreshold_abs int = int(requiredThreshold_abs_float)

							//for j := 0; j < len(myOpenBlockProposals); j++ {
							j := i

							//Check if enough peers have voted
							//if posPeerVotes[j]+negPeerVotes[j] < requValidators {
							//	fmt.Println("Not yet enough votes! Wait...")
							//	continue
							//}

							//if enough peers have voted, check who won
							if posPeerVotes[j] >= requiredThreshold_abs {
								fmt.Println("Proposal has enough votes and reached a majority: Accepted \n")

								fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
								fmt.Printf("Majority reached! Peer will will be removed from the network! Updating metrics...\n")
								fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

								// Reward is double deposit/stake: 3x to get back stake and then double it
								proposalReward := float64(3 * requStakeAddRemove)
								TokenBalanceStake := float64(ownPeerInfo["TokenBalance"].(float64))
								UpdateTokenBalance := TokenBalanceStake + proposalReward
								ownPeerInfo["TokenBalance"] = interface{}(UpdateTokenBalance)

								numberOfApprovedProposals := float64(ownPeerInfo["ApprovedProposals"].(float64))
								NewNumberOfApprovedProposals := numberOfApprovedProposals + float64(1)
								ownPeerInfo["ApprovedProposals"] = interface{}(NewNumberOfApprovedProposals)

								// broadcast with rest of peers
								var msg_8 strings.Builder
								senderID := ownPeerInfo["PeerID"].(string)
								senderID = senderID + string(";")
								switchcase := "FinalRemovalPeer;"
								msg_8.WriteString(senderID)
								msg_8.WriteString(switchcase)
								msg_8.WriteString(string(peer2Remove) + string(";"))
								msg_8.WriteString(proposer + string(";"))
								msg_8.WriteString(strconv.Itoa(posPeerVotes[j]))
								msg_8_send := msg_8.String()

								// broadcast with PubSub
								pubsub_msg := []byte(msg_8_send)
								go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

								// Send and wait for others to append
								fmt.Println("Sent to other peers!")

								// sender can update his list/metrics
								//remove from GlobalPeerList and network metrics!
								for k := 0; k < len(GlobalPeerList); k++ {
									if peer2Remove == GlobalPeerList[k] {
										copy(GlobalPeerList[k:], GlobalPeerList[k+1:])
										GlobalPeerList[len(GlobalPeerList)-1] = ""
										GlobalPeerList = GlobalPeerList[:len(GlobalPeerList)-1]
										continue
									}
								}

								// delete finished object from myOpenBlockProposals
								copy(myOpenPeerProposals[j:], myOpenPeerProposals[j+1:])
								myOpenPeerProposals[len(myOpenPeerProposals)-1] = ""
								myOpenPeerProposals = myOpenPeerProposals[:len(myOpenPeerProposals)-1]

								// also delete corresponding votes to this proposal!
								copy(posPeerVotes[j:], posPeerVotes[j+1:])
								posPeerVotes[len(posPeerVotes)-1] = 0
								posPeerVotes = posPeerVotes[:len(posPeerVotes)-1]
								copy(negPeerVotes[j:], negPeerVotes[j+1:])
								negPeerVotes[len(negPeerVotes)-1] = 0
								negPeerVotes = negPeerVotes[:len(negPeerVotes)-1]

								continue

							}

							if negPeerVotes[j] >= requiredThreshold_abs || ((posPeerVotes[j]+negPeerVotes[j] >= requValidators) && negPeerVotes[j] < requiredThreshold_abs) {
								fmt.Printf("Proposal has enough votes and reached a majority: Declined \n")

								fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
								fmt.Printf("No majority reached! Peer will stay in the network! Updating metrics...\n")
								fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

								// Reward is double deposit/stake: 3x to get back stake and then double it
								numberOfDeclinedProposals := float64(ownPeerInfo["DeclinedProposals"].(float64))
								NewNumberOfDeclinedProposals := numberOfDeclinedProposals + float64(1)
								ownPeerInfo["DeclinedProposals"] = interface{}(NewNumberOfDeclinedProposals)

								// Write into variable, to be sent and read later
								var msg_8 strings.Builder
								senderID := ownPeerInfo["PeerID"].(string)
								senderID = senderID + string(";")
								switchcase := "FinalRemovalPeerDeclined;"
								msg_8.WriteString(senderID)
								msg_8.WriteString(switchcase)
								msg_8.WriteString(string(proposer))
								msg_8_send := msg_8.String()

								// broadcast with PubSub
								pubsub_msg := []byte(msg_8_send)
								go PubSubP2P.Publish(pubsub_topic, pubsub_msg)

								// delete finished object from myOpenBlockProposals
								copy(myOpenPeerProposals[j:], myOpenPeerProposals[j+1:])
								myOpenPeerProposals[len(myOpenPeerProposals)-1] = ""
								myOpenPeerProposals = myOpenPeerProposals[:len(myOpenPeerProposals)-1]

								// also delete corresponding votes to this proposal!
								copy(posPeerVotes[j:], posPeerVotes[j+1:])
								posPeerVotes[len(posPeerVotes)-1] = 0
								posPeerVotes = posPeerVotes[:len(posPeerVotes)-1]
								copy(negPeerVotes[j:], negPeerVotes[j+1:])
								negPeerVotes[len(negPeerVotes)-1] = 0
								negPeerVotes = negPeerVotes[:len(negPeerVotes)-1]

								continue

							} //Declined

						} //belongs to proposal i
					} // for loop own proposals

					// peer received a vote for an already finsihed proposal
					if ownProposal_notInList5 == true {
						// after check; delete finished object from openVotesOnNewBlockProposals
						fmt.Println("Vote cannot be assigned to an open proposal! Delete...")
						copy(openVotesRemovePeerAccountProposals[0:], openVotesRemovePeerAccountProposals[1:])
						openVotesRemovePeerAccountProposals[len(openVotesRemovePeerAccountProposals)-1] = ""
						openVotesRemovePeerAccountProposals = openVotesRemovePeerAccountProposals[:len(openVotesRemovePeerAccountProposals)-1]

						continue
					}

				} else { //author is not own peer ID = not creator

					// delete finished object from openVotesOnNewBlockProposals
					copy(openVotesRemovePeerAccountProposals[0:], openVotesRemovePeerAccountProposals[1:])
					openVotesRemovePeerAccountProposals[len(openVotesRemovePeerAccountProposals)-1] = ""
					openVotesRemovePeerAccountProposals = openVotesRemovePeerAccountProposals[:len(openVotesRemovePeerAccountProposals)-1]

				}
			}
		} //queue votes remove existing peer

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// remove other peer accepted
		if len(openFinalRemovePeerAccountProposals) > 0 {
			// read from queue:
			currentContent := openFinalRemovePeerAccountProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]
			peer2Remove := receivedContent_parsed[2]
			majority := receivedContent_parsed[4]
			majority_int, _ := strconv.Atoi(majority)
			//proposer := receivedContent_parsed[3]

			if switchcase == "FinalRemovalPeer" {

				if pid_own != peer2Remove {

					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Printf("Proposal accepted: The network decided to remove a peer:\n")
					fmt.Printf("Peer <%s> will be removed from the network! %v of %v peers in the network agreed! \n", peer2Remove, majority_int+1, len(GlobalPeerList))
					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

					//safe in removal list: check with myLocalPeersbefore
					removedPeers = append(removedPeers, peer2Remove)

					//remove from GlobalPeerList and network metrics!
					for k := 0; k < len(GlobalPeerList); k++ {
						if peer2Remove == GlobalPeerList[k] {
							copy(GlobalPeerList[k:], GlobalPeerList[k+1:])
							GlobalPeerList[len(GlobalPeerList)-1] = ""
							GlobalPeerList = GlobalPeerList[:len(GlobalPeerList)-1]
							continue
						}
					}

					// delete finished object from openVotesOnNewBlockProposals
					copy(openFinalRemovePeerAccountProposals[0:], openFinalRemovePeerAccountProposals[1:])
					openFinalRemovePeerAccountProposals[len(openFinalRemovePeerAccountProposals)-1] = ""
					openFinalRemovePeerAccountProposals = openFinalRemovePeerAccountProposals[:len(openFinalRemovePeerAccountProposals)-1]

					continue

				} else if pid_own == peer2Remove {

					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Printf("The network decided to remove you! Your account will be deleted and you can only come back by invitation and majority vote!\n")
					fmt.Printf("%v of %v peers in the network agreed to remove your account! \n", majority_int+1, len(GlobalPeerList))
					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

					// delete finished object from openVotesOnNewBlockProposals
					copy(openFinalRemovePeerAccountProposals[0:], openFinalRemovePeerAccountProposals[1:])
					openFinalRemovePeerAccountProposals[len(openFinalRemovePeerAccountProposals)-1] = ""
					openFinalRemovePeerAccountProposals = openFinalRemovePeerAccountProposals[:len(openFinalRemovePeerAccountProposals)-1]

					// Unsubscribe from PubSub topic
					pubsub_subsrc.Cancel()
				}

			}
		} //queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// remove other peer declined
		if len(openDeclinedRemovePeerAccountProposals) > 0 {
			// read from queue:
			currentContent := openDeclinedRemovePeerAccountProposals[0]
			// parse incoming string: sender ; case ; ....rest later
			receivedContent_parsed := strings.Split(currentContent, ";")
			//sender := receivedContent_parsed[0]
			switchcase := receivedContent_parsed[1]
			peer2Remove := receivedContent_parsed[2]
			//proposer := receivedContent_parsed[3]

			if switchcase == "FinalRemovalPeerDeclined" {

				if pid_own != peer2Remove {
					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Printf("Proposal declined! The network decided to not remove a peer!\n")
					fmt.Printf("Peer <%s> will saty in the network!\n", peer2Remove)
					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")

				} else if pid_own == peer2Remove {
					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
					fmt.Printf("Proposal declined! The network decided to not remove you!:\n")
					fmt.Printf("You will stay in the network!\n")
					fmt.Printf("\x1b[32m++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\x1b[0m \n")
				}

			}

			// delete finished object from openVotesOnNewBlockProposals
			copy(openDeclinedRemovePeerAccountProposals[0:], openDeclinedRemovePeerAccountProposals[1:])
			openDeclinedRemovePeerAccountProposals[len(openDeclinedRemovePeerAccountProposals)-1] = ""
			openDeclinedRemovePeerAccountProposals = openDeclinedRemovePeerAccountProposals[:len(openDeclinedRemovePeerAccountProposals)-1]
			continue

		} //queue

		//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

	} //for loop

} // end readWriteProcessData

//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// MAIN function
//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

func main() {

	// Create first empty (genesis) block and append to empty blockchain
	t := time.Now()
	t_block := t.Format(time.RFC850) //string, use instead of t.String()
	genesisBlock := Block{}
	genesisBlock = Block{0, t_block, "", "", "", "", "", "", calculateHash(genesisBlock)}
	Blockchain = append(Blockchain, genesisBlock)

	// LibP2P code uses golog to log messages. They log with different
	// string IDs (i.e. "swarm"). You can control the verbosity level for all loggers.
	// Change to DEBUG for extra info
	golog.SetAllLoggers(gologging.INFO)

	// Parse options from the command line
	listenF := flag.Int("l", 0, "wait for incoming connections")
	target := flag.String("d", "", "target peer to dial")
	secio := flag.Bool("secio", false, "enable secio")
	seed := flag.Int64("seed", 0, "set random seed for id generation")
	flag.Parse()

	if *listenF == 0 {
		log.Fatal("Please provide a port to bind on with -l")
	}

	// Make a host that listens on the given multiaddress
	basicHostMain, fullAddress, newPeer_parsed, err := makeBasicHost(*listenF, *secio, *seed)
	if err != nil {
		log.Fatal(err)
	}

	//Create a pubsub instance: GossipSub is more efficient than FloodSub!
	PubSubP2P, _ = pubsub.NewGossipSub(context.Background(), basicHostMain)
	//PubSubP2P, _ = pubsub.NewFloodSub(context.Background(), basicHostMain)

	// create and subscribe to topic
	pubsub_subsrc, _ = PubSubP2P.Subscribe(pubsub_topic)
	log.Printf("PubSub initialized and subscribed to topic %s.\n", pubsub_topic)

	// Check if only acting as host or connecting with others
	if *target == "" {

		//get peer information
		var ownPeerInfo map[string]interface{}
		if err := json.Unmarshal(newPeer_parsed, &ownPeerInfo); err != nil {
			panic(err)
		}
		ConnectedPeers = append(ConnectedPeers, ownPeerInfo)
		log.Println("Peer added! Listening for connections...")

		// Set a stream handler on host A. /p2p/1.0.0 is a user-defined protocol name.
		// This function is called on the local peer when a remote peer initiate a
		// connection and starts a stream with the local peer.
		basicHostMain.SetStreamHandler("/p2p/1.0.0", handleStream)

		select {} // hang forever

		/**** This is where the listener code ends ****/

		//++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

		// the rest of the code is executed by the connecting nodes/terminals
	} else {

		//get peer information
		var ownPeerInfo map[string]interface{}
		if err := json.Unmarshal(newPeer_parsed, &ownPeerInfo); err != nil {
			panic(err)
		}
		ConnectedPeers = append(ConnectedPeers, ownPeerInfo)
		log.Println("Peer added! Connecting...")

		// This function is called on the local peer when a remote peer initiate a
		// connection and starts a stream with the local peer.
		basicHostMain.SetStreamHandler("/p2p/1.0.0", handleStream) //"Got a new Stream"

		// The following code extracts target's peer ID from the given multiaddress
		// In IPFS, the crypthographic peerID is a SHA-256 multihash of a public keys
		// The public/private keypair is created using RSA
		// Here the peerID is based on the private key!
		ipfsaddr_target, err := multiaddress.NewMultiaddr(*target)
		if err != nil {
			log.Fatalln(err)
		}

		//string
		pid_target, err := ipfsaddr_target.ValueForProtocol(multiaddress.P_IPFS)
		if err != nil {
			log.Fatalln(err)
		}

		// En-De-Codeing: b58
		peerid_target, err := peer.IDB58Decode(pid_target)
		if err != nil {
			log.Fatalln(err)
		}

		// Decapsulate the /ipfs/<peerID> part from the target
		// /ip4/<a.b.c.d>/ipfs/<peer> becomes /ip4/<a.b.c.d>
		targetPeerAddr, _ := multiaddress.NewMultiaddr(
			fmt.Sprintf("/ipfs/%s", peer.IDB58Encode(peerid_target)))
		targetAddr := ipfsaddr_target.Decapsulate(targetPeerAddr)

		// We have a peer ID and a targetAddr so we add it to the peerstore so LibP2P knows how to contact it
		// Peerstore manages the sets of peers, their addresses and further metadata
		basicHostMain.Peerstore().AddAddr(peerid_target, targetAddr, pstore.PermanentAddrTTL)

		// make/open a new stream from host B to host A
		// this stream will be handled by handleStream on the other end (host A)
		// by the handler set above because we use the same /p2p/1.0.0 protocol
		//log.Println("Opening stream...")
		stream, err := basicHostMain.NewStream(context.Background(), peerid_target, "/p2p/1.0.0")
		if err != nil {
			log.Println("Failed to open new stream!")
			log.Fatalln(err)
		} else {
			log.Printf("Stream opened:%v\n", stream)
		}

		// Calculate your own peerID based on your fullAddress
		fullAddrString := fullAddress.String() // fullAddrString is a base58 string
		ipfsaddr_own, err := multiaddress.NewMultiaddr(fullAddrString)
		if err != nil {
			log.Fatalln(err)
		}

		//string
		pid_own, err := ipfsaddr_own.ValueForProtocol(multiaddress.P_IPFS)
		if err != nil {
			log.Fatalln(err)
		}

		// En-De-Codeing: IDB58Decode returns a b58-decoded peer
		peerid_own, err := peer.IDB58Decode(pid_own)
		if err != nil {
			log.Fatalln(err)
		}

		// Decapsulate the /ipfs/<peerID> part from the own
		// /ip4/<a.b.c.d>/ipfs/<peer> becomes /ip4/<a.b.c.d>
		ownPeerAddr, _ := multiaddress.NewMultiaddr(
			fmt.Sprintf("/ipfs/%s", peer.IDB58Encode(peerid_own)))
		ownAddr := ipfsaddr_own.Decapsulate(ownPeerAddr)

		// We have a peer ID and a targetAddr so we add it to the peerstore
		// Peerstore manages the sets of peers, their addresses and further metadata
		basicHostMain.Peerstore().AddAddr(peerid_own, ownAddr, pstore.PermanentAddrTTL)

		//Inform the user
		log.Printf("You are now directly connected with peerID: %s\n", peerid_target)
		log.Printf("Your own peerID is: %s\n", peerid_own)

		// Create a thread to read and write and process data
		go handleTerminalInput(pubsub_subsrc, ownPeerInfo)
		go readWriteProcessData(pubsub_subsrc, ownPeerInfo)

		// Keep Chain open forever
		select {}
	}
} // end main
