module Graphics.Ubigraph
    ( Url
    , VertexId
    , EdgeId
    , defaultServer
    , clear
    , newVertex
    , newEdge
    , removeVertex
    , removeEdge
    , newVertexWithId
    , newEdgeWithId
    , setVertexAttribute
    , setEdgeAttribute
    ) where

import Network.XmlRpc.Client

type Url = String
type VertexId = Int
type EdgeId = Int

defaultServer :: Url
defaultServer = "http://127.0.0.1:20738/RPC2"

clear :: Url -> IO ()
clear url = void (remote url "ubigraph.clear")

newVertex :: Url -> IO VertexId
newVertex url = remote url "ubigraph.new_vertex"

newEdge :: Url -> VertexId -> VertexId -> IO EdgeId
newEdge url = remote url "ubigraph.new_edge"

removeVertex :: Url -> VertexId -> IO ()
removeVertex url vid = void (remote url "ubigraph.remove_vertex" vid)

removeEdge :: Url -> EdgeId -> IO ()
removeEdge url eid= void (remote url "ubigraph.remove_edge" eid)

newVertexWithId :: Url -> VertexId -> IO Bool
newVertexWithId url vid = zeroOnSuccess (remote url "ubigraph.new_vertex_w_id" vid)

newEdgeWithId :: Url -> EdgeId -> VertexId -> VertexId -> IO Bool
newEdgeWithId url eid x y = zeroOnSuccess (remote url "ubigraph.new_edge_w_id" eid x y)

setVertexAttribute :: Url -> VertexId -> String -> String -> IO Bool
setVertexAttribute url vid attr val = zeroOnSuccess (remote url "ubigraph.set_vertex_attribute" vid attr val)

setEdgeAttribute :: Url -> VertexId -> String -> String -> IO Bool
setEdgeAttribute url eid attr val = zeroOnSuccess (remote url "ubigraph.set_edge_attribute" eid attr val)

void :: IO Int -> IO ()
void m = m >> return ()

zeroOnSuccess :: IO Int -> IO Bool
zeroOnSuccess = fmap (==0)
